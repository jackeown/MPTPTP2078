%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:20 EST 2020

% Result     : Theorem 1.83s
% Output     : Refutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 297 expanded)
%              Number of leaves         :   11 (  99 expanded)
%              Depth                    :   20
%              Number of atoms          :   51 ( 298 expanded)
%              Number of equality atoms :   50 ( 297 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3434,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3329,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

fof(f3329,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK1,sK2) ),
    inference(superposition,[],[f23,f2263])).

fof(f2263,plain,(
    ! [X47,X45,X46,X44] : k2_enumset1(X44,X46,X47,X45) = k2_enumset1(X46,X45,X44,X47) ),
    inference(superposition,[],[f2181,f31])).

fof(f2181,plain,(
    ! [X30,X28,X31,X29] : k2_enumset1(X28,X30,X29,X31) = k2_enumset1(X29,X30,X28,X31) ),
    inference(superposition,[],[f1184,f613])).

fof(f613,plain,(
    ! [X50,X48,X51,X49] : k3_enumset1(X48,X49,X49,X50,X51) = k2_enumset1(X49,X50,X48,X51) ),
    inference(forward_demodulation,[],[f605,f367])).

fof(f367,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3)) ),
    inference(forward_demodulation,[],[f353,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f353,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3)) ),
    inference(superposition,[],[f350,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X2,X1) ),
    inference(superposition,[],[f30,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

fof(f350,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(forward_demodulation,[],[f349,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f349,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(superposition,[],[f178,f32])).

fof(f178,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(forward_demodulation,[],[f177,f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f177,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(superposition,[],[f36,f33])).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

fof(f605,plain,(
    ! [X50,X48,X51,X49] : k3_enumset1(X48,X49,X49,X50,X51) = k2_xboole_0(k1_enumset1(X49,X48,X50),k1_tarski(X51)) ),
    inference(superposition,[],[f350,f554])).

fof(f554,plain,(
    ! [X39,X38,X40] : k2_enumset1(X38,X39,X39,X40) = k1_enumset1(X39,X38,X40) ),
    inference(forward_demodulation,[],[f551,f552])).

fof(f552,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(forward_demodulation,[],[f541,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X2,X0,X1) = k1_enumset1(X0,X2,X1) ),
    inference(superposition,[],[f31,f55])).

fof(f541,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X1,X0,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(superposition,[],[f367,f25])).

fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f551,plain,(
    ! [X39,X38,X40] : k2_enumset1(X38,X39,X39,X40) = k2_xboole_0(k2_tarski(X39,X38),k1_tarski(X40)) ),
    inference(superposition,[],[f367,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0) ),
    inference(superposition,[],[f28,f25])).

fof(f28,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

fof(f1184,plain,(
    ! [X134,X136,X135,X137] : k3_enumset1(X134,X135,X135,X136,X137) = k2_enumset1(X134,X136,X135,X137) ),
    inference(forward_demodulation,[],[f1163,f367])).

fof(f1163,plain,(
    ! [X134,X136,X135,X137] : k3_enumset1(X134,X135,X135,X136,X137) = k2_xboole_0(k1_enumset1(X134,X135,X136),k1_tarski(X137)) ),
    inference(superposition,[],[f350,f678])).

fof(f678,plain,(
    ! [X45,X46,X44] : k1_enumset1(X44,X45,X46) = k2_enumset1(X44,X45,X45,X46) ),
    inference(forward_demodulation,[],[f672,f552])).

fof(f672,plain,(
    ! [X45,X46,X44] : k2_enumset1(X44,X45,X45,X46) = k2_xboole_0(k2_tarski(X44,X45),k1_tarski(X46)) ),
    inference(superposition,[],[f367,f609])).

fof(f609,plain,(
    ! [X28,X29] : k1_enumset1(X28,X29,X29) = k2_tarski(X28,X29) ),
    inference(forward_demodulation,[],[f592,f43])).

fof(f592,plain,(
    ! [X28,X29] : k1_enumset1(X28,X29,X29) = k1_enumset1(X29,X28,X28) ),
    inference(superposition,[],[f554,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X1,X2,X0) = k1_enumset1(X0,X2,X1) ),
    inference(superposition,[],[f31,f55])).

fof(f23,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:42:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (31863)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (31869)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (31869)Refutation not found, incomplete strategy% (31869)------------------------------
% 0.22/0.48  % (31869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (31872)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (31870)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (31862)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (31861)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (31869)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (31869)Memory used [KB]: 10618
% 0.22/0.48  % (31869)Time elapsed: 0.062 s
% 0.22/0.48  % (31869)------------------------------
% 0.22/0.48  % (31869)------------------------------
% 0.22/0.48  % (31858)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (31864)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (31868)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (31871)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (31866)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (31860)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  % (31859)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.51  % (31873)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (31874)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.51  % (31875)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.52  % (31867)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.52  % (31865)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.83/0.59  % (31861)Refutation found. Thanks to Tanya!
% 1.83/0.59  % SZS status Theorem for theBenchmark
% 1.83/0.60  % SZS output start Proof for theBenchmark
% 1.83/0.60  fof(f3434,plain,(
% 1.83/0.60    $false),
% 1.83/0.60    inference(subsumption_resolution,[],[f3329,f31])).
% 1.83/0.60  fof(f31,plain,(
% 1.83/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f6])).
% 1.83/0.60  fof(f6,axiom,(
% 1.83/0.60    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).
% 1.83/0.60  fof(f3329,plain,(
% 1.83/0.60    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK1,sK2)),
% 1.83/0.60    inference(superposition,[],[f23,f2263])).
% 1.83/0.60  fof(f2263,plain,(
% 1.83/0.60    ( ! [X47,X45,X46,X44] : (k2_enumset1(X44,X46,X47,X45) = k2_enumset1(X46,X45,X44,X47)) )),
% 1.83/0.60    inference(superposition,[],[f2181,f31])).
% 1.83/0.60  fof(f2181,plain,(
% 1.83/0.60    ( ! [X30,X28,X31,X29] : (k2_enumset1(X28,X30,X29,X31) = k2_enumset1(X29,X30,X28,X31)) )),
% 1.83/0.60    inference(superposition,[],[f1184,f613])).
% 1.83/0.60  fof(f613,plain,(
% 1.83/0.60    ( ! [X50,X48,X51,X49] : (k3_enumset1(X48,X49,X49,X50,X51) = k2_enumset1(X49,X50,X48,X51)) )),
% 1.83/0.60    inference(forward_demodulation,[],[f605,f367])).
% 1.83/0.60  fof(f367,plain,(
% 1.83/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3))) )),
% 1.83/0.60    inference(forward_demodulation,[],[f353,f32])).
% 1.83/0.60  fof(f32,plain,(
% 1.83/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f14])).
% 1.83/0.60  fof(f14,axiom,(
% 1.83/0.60    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.83/0.60  fof(f353,plain,(
% 1.83/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3))) )),
% 1.83/0.60    inference(superposition,[],[f350,f55])).
% 1.83/0.60  fof(f55,plain,(
% 1.83/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X2,X1)) )),
% 1.83/0.60    inference(superposition,[],[f30,f29])).
% 1.83/0.60  fof(f29,plain,(
% 1.83/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f13])).
% 1.83/0.60  fof(f13,axiom,(
% 1.83/0.60    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.83/0.60  fof(f30,plain,(
% 1.83/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f5])).
% 1.83/0.60  fof(f5,axiom,(
% 1.83/0.60    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).
% 1.83/0.60  fof(f350,plain,(
% 1.83/0.60    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 1.83/0.60    inference(forward_demodulation,[],[f349,f33])).
% 1.83/0.60  fof(f33,plain,(
% 1.83/0.60    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f15])).
% 1.83/0.60  fof(f15,axiom,(
% 1.83/0.60    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.83/0.60  fof(f349,plain,(
% 1.83/0.60    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 1.83/0.60    inference(superposition,[],[f178,f32])).
% 1.83/0.60  fof(f178,plain,(
% 1.83/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 1.83/0.60    inference(forward_demodulation,[],[f177,f34])).
% 1.83/0.60  fof(f34,plain,(
% 1.83/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f16])).
% 1.83/0.60  fof(f16,axiom,(
% 1.83/0.60    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.83/0.60  fof(f177,plain,(
% 1.83/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 1.83/0.60    inference(superposition,[],[f36,f33])).
% 1.83/0.60  fof(f36,plain,(
% 1.83/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 1.83/0.60    inference(cnf_transformation,[],[f7])).
% 1.83/0.60  fof(f7,axiom,(
% 1.83/0.60    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).
% 1.83/0.60  fof(f605,plain,(
% 1.83/0.60    ( ! [X50,X48,X51,X49] : (k3_enumset1(X48,X49,X49,X50,X51) = k2_xboole_0(k1_enumset1(X49,X48,X50),k1_tarski(X51))) )),
% 1.83/0.60    inference(superposition,[],[f350,f554])).
% 1.83/0.60  fof(f554,plain,(
% 1.83/0.60    ( ! [X39,X38,X40] : (k2_enumset1(X38,X39,X39,X40) = k1_enumset1(X39,X38,X40)) )),
% 1.83/0.60    inference(forward_demodulation,[],[f551,f552])).
% 1.83/0.60  fof(f552,plain,(
% 1.83/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.83/0.60    inference(forward_demodulation,[],[f541,f70])).
% 1.83/0.60  fof(f70,plain,(
% 1.83/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X2,X0,X1) = k1_enumset1(X0,X2,X1)) )),
% 1.83/0.60    inference(superposition,[],[f31,f55])).
% 1.83/0.60  fof(f541,plain,(
% 1.83/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X1,X0,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.83/0.60    inference(superposition,[],[f367,f25])).
% 1.83/0.60  fof(f25,plain,(
% 1.83/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f12])).
% 1.83/0.60  fof(f12,axiom,(
% 1.83/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.83/0.60  fof(f551,plain,(
% 1.83/0.60    ( ! [X39,X38,X40] : (k2_enumset1(X38,X39,X39,X40) = k2_xboole_0(k2_tarski(X39,X38),k1_tarski(X40))) )),
% 1.83/0.60    inference(superposition,[],[f367,f43])).
% 1.83/0.60  fof(f43,plain,(
% 1.83/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)) )),
% 1.83/0.60    inference(superposition,[],[f28,f25])).
% 1.83/0.60  fof(f28,plain,(
% 1.83/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f4])).
% 1.83/0.60  fof(f4,axiom,(
% 1.83/0.60    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).
% 1.83/0.60  fof(f1184,plain,(
% 1.83/0.60    ( ! [X134,X136,X135,X137] : (k3_enumset1(X134,X135,X135,X136,X137) = k2_enumset1(X134,X136,X135,X137)) )),
% 1.83/0.60    inference(forward_demodulation,[],[f1163,f367])).
% 1.83/0.60  fof(f1163,plain,(
% 1.83/0.60    ( ! [X134,X136,X135,X137] : (k3_enumset1(X134,X135,X135,X136,X137) = k2_xboole_0(k1_enumset1(X134,X135,X136),k1_tarski(X137))) )),
% 1.83/0.60    inference(superposition,[],[f350,f678])).
% 1.83/0.60  fof(f678,plain,(
% 1.83/0.60    ( ! [X45,X46,X44] : (k1_enumset1(X44,X45,X46) = k2_enumset1(X44,X45,X45,X46)) )),
% 1.83/0.60    inference(forward_demodulation,[],[f672,f552])).
% 1.83/0.60  fof(f672,plain,(
% 1.83/0.60    ( ! [X45,X46,X44] : (k2_enumset1(X44,X45,X45,X46) = k2_xboole_0(k2_tarski(X44,X45),k1_tarski(X46))) )),
% 1.83/0.60    inference(superposition,[],[f367,f609])).
% 1.83/0.60  fof(f609,plain,(
% 1.83/0.60    ( ! [X28,X29] : (k1_enumset1(X28,X29,X29) = k2_tarski(X28,X29)) )),
% 1.83/0.60    inference(forward_demodulation,[],[f592,f43])).
% 1.83/0.60  fof(f592,plain,(
% 1.83/0.60    ( ! [X28,X29] : (k1_enumset1(X28,X29,X29) = k1_enumset1(X29,X28,X28)) )),
% 1.83/0.60    inference(superposition,[],[f554,f65])).
% 1.83/0.60  fof(f65,plain,(
% 1.83/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X1,X2,X0) = k1_enumset1(X0,X2,X1)) )),
% 1.83/0.60    inference(superposition,[],[f31,f55])).
% 1.83/0.60  fof(f23,plain,(
% 1.83/0.60    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 1.83/0.60    inference(cnf_transformation,[],[f22])).
% 1.83/0.60  fof(f22,plain,(
% 1.83/0.60    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 1.83/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f21])).
% 1.83/0.60  fof(f21,plain,(
% 1.83/0.60    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 1.83/0.60    introduced(choice_axiom,[])).
% 1.83/0.60  fof(f20,plain,(
% 1.83/0.60    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 1.83/0.60    inference(ennf_transformation,[],[f19])).
% 1.83/0.60  fof(f19,negated_conjecture,(
% 1.83/0.60    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 1.83/0.60    inference(negated_conjecture,[],[f18])).
% 1.83/0.60  fof(f18,conjecture,(
% 1.83/0.60    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).
% 1.83/0.60  % SZS output end Proof for theBenchmark
% 1.83/0.60  % (31861)------------------------------
% 1.83/0.60  % (31861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.60  % (31861)Termination reason: Refutation
% 1.83/0.60  
% 1.83/0.60  % (31861)Memory used [KB]: 6268
% 1.83/0.60  % (31861)Time elapsed: 0.173 s
% 1.83/0.60  % (31861)------------------------------
% 1.83/0.60  % (31861)------------------------------
% 1.83/0.60  % (31857)Success in time 0.234 s
%------------------------------------------------------------------------------
