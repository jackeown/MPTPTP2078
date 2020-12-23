%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:42 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   34 (  46 expanded)
%              Number of leaves         :    9 (  15 expanded)
%              Depth                    :   12
%              Number of atoms          :   35 (  47 expanded)
%              Number of equality atoms :   34 (  46 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f188,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f181])).

fof(f181,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f18,f135])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(forward_demodulation,[],[f132,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f132,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(superposition,[],[f118,f19])).

fof(f19,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f118,plain,(
    ! [X14,X12,X15,X13,X16] : k3_enumset1(X12,X13,X14,X15,X16) = k2_xboole_0(k2_tarski(X12,X13),k1_enumset1(X14,X15,X16)) ),
    inference(forward_demodulation,[],[f117,f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f117,plain,(
    ! [X14,X12,X15,X13,X16] : k2_xboole_0(k2_tarski(X12,X13),k1_enumset1(X14,X15,X16)) = k2_xboole_0(k1_tarski(X12),k2_enumset1(X13,X14,X15,X16)) ),
    inference(forward_demodulation,[],[f116,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X3,X0,X0,X1,X2) = k2_enumset1(X3,X0,X1,X2) ),
    inference(forward_demodulation,[],[f36,f24])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X3,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f26,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f116,plain,(
    ! [X14,X12,X15,X13,X16] : k2_xboole_0(k1_tarski(X12),k3_enumset1(X13,X14,X14,X15,X16)) = k2_xboole_0(k2_tarski(X12,X13),k1_enumset1(X14,X15,X16)) ),
    inference(forward_demodulation,[],[f115,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f115,plain,(
    ! [X14,X12,X15,X13,X16] : k2_xboole_0(k1_tarski(X12),k3_enumset1(X13,X14,X14,X15,X16)) = k2_xboole_0(k1_enumset1(X12,X12,X13),k1_enumset1(X14,X15,X16)) ),
    inference(forward_demodulation,[],[f100,f23])).

fof(f100,plain,(
    ! [X14,X12,X15,X13,X16] : k2_xboole_0(k1_tarski(X12),k3_enumset1(X13,X14,X14,X15,X16)) = k2_xboole_0(k2_enumset1(X12,X12,X12,X13),k1_enumset1(X14,X15,X16)) ),
    inference(superposition,[],[f49,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(superposition,[],[f42,f19])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(superposition,[],[f28,f20])).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_enumset1)).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X3,X4,X5,X6,X0,X0,X1,X2) = k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f29,f23])).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(f18,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:08:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.45  % (19082)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (19087)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (19087)Refutation not found, incomplete strategy% (19087)------------------------------
% 0.20/0.47  % (19087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (19087)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (19087)Memory used [KB]: 10490
% 0.20/0.47  % (19087)Time elapsed: 0.049 s
% 0.20/0.47  % (19087)------------------------------
% 0.20/0.47  % (19087)------------------------------
% 0.20/0.48  % (19080)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (19083)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (19088)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (19076)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (19090)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (19089)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.50  % (19091)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (19077)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.50  % (19092)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.51  % (19085)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.51  % (19078)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.51  % (19081)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.51  % (19079)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.51  % (19086)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 1.27/0.52  % (19084)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.27/0.53  % (19093)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.40/0.53  % (19079)Refutation found. Thanks to Tanya!
% 1.40/0.53  % SZS status Theorem for theBenchmark
% 1.40/0.53  % SZS output start Proof for theBenchmark
% 1.40/0.53  fof(f188,plain,(
% 1.40/0.53    $false),
% 1.40/0.53    inference(trivial_inequality_removal,[],[f181])).
% 1.40/0.53  fof(f181,plain,(
% 1.40/0.53    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3)),
% 1.40/0.53    inference(superposition,[],[f18,f135])).
% 1.40/0.53  fof(f135,plain,(
% 1.40/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.40/0.53    inference(forward_demodulation,[],[f132,f24])).
% 1.40/0.53  fof(f24,plain,(
% 1.40/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 1.40/0.53    inference(cnf_transformation,[],[f5])).
% 1.40/0.53  fof(f5,axiom,(
% 1.40/0.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 1.40/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 1.40/0.53  fof(f132,plain,(
% 1.40/0.53    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.40/0.53    inference(superposition,[],[f118,f19])).
% 1.40/0.53  fof(f19,plain,(
% 1.40/0.53    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.40/0.53    inference(cnf_transformation,[],[f10])).
% 1.40/0.53  fof(f10,axiom,(
% 1.40/0.53    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.40/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.40/0.53  fof(f118,plain,(
% 1.40/0.53    ( ! [X14,X12,X15,X13,X16] : (k3_enumset1(X12,X13,X14,X15,X16) = k2_xboole_0(k2_tarski(X12,X13),k1_enumset1(X14,X15,X16))) )),
% 1.40/0.53    inference(forward_demodulation,[],[f117,f26])).
% 1.40/0.53  fof(f26,plain,(
% 1.40/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 1.40/0.53    inference(cnf_transformation,[],[f6])).
% 1.40/0.53  fof(f6,axiom,(
% 1.40/0.53    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 1.40/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 1.40/0.53  fof(f117,plain,(
% 1.40/0.53    ( ! [X14,X12,X15,X13,X16] : (k2_xboole_0(k2_tarski(X12,X13),k1_enumset1(X14,X15,X16)) = k2_xboole_0(k1_tarski(X12),k2_enumset1(X13,X14,X15,X16))) )),
% 1.40/0.53    inference(forward_demodulation,[],[f116,f38])).
% 1.40/0.53  fof(f38,plain,(
% 1.40/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X3,X0,X0,X1,X2) = k2_enumset1(X3,X0,X1,X2)) )),
% 1.40/0.53    inference(forward_demodulation,[],[f36,f24])).
% 1.40/0.53  fof(f36,plain,(
% 1.40/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X3,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2))) )),
% 1.40/0.53    inference(superposition,[],[f26,f23])).
% 1.40/0.53  fof(f23,plain,(
% 1.40/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.40/0.53    inference(cnf_transformation,[],[f12])).
% 1.40/0.53  fof(f12,axiom,(
% 1.40/0.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.40/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.40/0.53  fof(f116,plain,(
% 1.40/0.53    ( ! [X14,X12,X15,X13,X16] : (k2_xboole_0(k1_tarski(X12),k3_enumset1(X13,X14,X14,X15,X16)) = k2_xboole_0(k2_tarski(X12,X13),k1_enumset1(X14,X15,X16))) )),
% 1.40/0.53    inference(forward_demodulation,[],[f115,f20])).
% 1.40/0.53  fof(f20,plain,(
% 1.40/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.40/0.53    inference(cnf_transformation,[],[f11])).
% 1.40/0.53  fof(f11,axiom,(
% 1.40/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.40/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.40/0.53  fof(f115,plain,(
% 1.40/0.53    ( ! [X14,X12,X15,X13,X16] : (k2_xboole_0(k1_tarski(X12),k3_enumset1(X13,X14,X14,X15,X16)) = k2_xboole_0(k1_enumset1(X12,X12,X13),k1_enumset1(X14,X15,X16))) )),
% 1.40/0.53    inference(forward_demodulation,[],[f100,f23])).
% 1.40/0.53  fof(f100,plain,(
% 1.40/0.53    ( ! [X14,X12,X15,X13,X16] : (k2_xboole_0(k1_tarski(X12),k3_enumset1(X13,X14,X14,X15,X16)) = k2_xboole_0(k2_enumset1(X12,X12,X12,X13),k1_enumset1(X14,X15,X16))) )),
% 1.40/0.53    inference(superposition,[],[f49,f67])).
% 1.40/0.53  fof(f67,plain,(
% 1.40/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.40/0.53    inference(superposition,[],[f42,f19])).
% 1.40/0.53  fof(f42,plain,(
% 1.40/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))) )),
% 1.40/0.53    inference(superposition,[],[f28,f20])).
% 1.40/0.53  fof(f28,plain,(
% 1.40/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7))) )),
% 1.40/0.53    inference(cnf_transformation,[],[f8])).
% 1.40/0.53  fof(f8,axiom,(
% 1.40/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7))),
% 1.40/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_enumset1)).
% 1.40/0.53  fof(f49,plain,(
% 1.40/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X3,X4,X5,X6,X0,X0,X1,X2) = k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_enumset1(X0,X1,X2))) )),
% 1.40/0.53    inference(superposition,[],[f29,f23])).
% 1.40/0.53  fof(f29,plain,(
% 1.40/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 1.40/0.53    inference(cnf_transformation,[],[f3])).
% 1.40/0.53  fof(f3,axiom,(
% 1.40/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 1.40/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).
% 1.40/0.53  fof(f18,plain,(
% 1.40/0.53    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 1.40/0.53    inference(cnf_transformation,[],[f17])).
% 1.40/0.53  fof(f17,plain,(
% 1.40/0.53    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 1.40/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f16])).
% 1.40/0.53  fof(f16,plain,(
% 1.40/0.53    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 1.40/0.53    introduced(choice_axiom,[])).
% 1.40/0.53  fof(f15,plain,(
% 1.40/0.53    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3)),
% 1.40/0.53    inference(ennf_transformation,[],[f14])).
% 1.40/0.53  fof(f14,negated_conjecture,(
% 1.40/0.53    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.40/0.53    inference(negated_conjecture,[],[f13])).
% 1.40/0.53  fof(f13,conjecture,(
% 1.40/0.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.40/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.40/0.53  % SZS output end Proof for theBenchmark
% 1.40/0.53  % (19079)------------------------------
% 1.40/0.53  % (19079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.53  % (19079)Termination reason: Refutation
% 1.40/0.53  
% 1.40/0.53  % (19079)Memory used [KB]: 1791
% 1.40/0.53  % (19079)Time elapsed: 0.122 s
% 1.40/0.53  % (19079)------------------------------
% 1.40/0.53  % (19079)------------------------------
% 1.40/0.54  % (19075)Success in time 0.176 s
%------------------------------------------------------------------------------
