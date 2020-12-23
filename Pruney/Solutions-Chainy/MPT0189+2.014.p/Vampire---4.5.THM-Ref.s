%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:19 EST 2020

% Result     : Theorem 2.33s
% Output     : Refutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   47 (  63 expanded)
%              Number of leaves         :   13 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :   48 (  64 expanded)
%              Number of equality atoms :   47 (  63 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8016,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7945,f149])).

fof(f149,plain,(
    ! [X14,X17,X15,X16] : k2_enumset1(X14,X15,X17,X16) = k2_enumset1(X14,X16,X17,X15) ),
    inference(superposition,[],[f56,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

fof(f56,plain,(
    ! [X14,X12,X13,X11] : k2_enumset1(X11,X13,X12,X14) = k2_enumset1(X11,X12,X14,X13) ),
    inference(superposition,[],[f34,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).

fof(f7945,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1) ),
    inference(superposition,[],[f26,f5039])).

fof(f5039,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X6,X5) ),
    inference(superposition,[],[f1482,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f1482,plain,(
    ! [X12,X10,X13,X11] : k3_enumset1(X10,X10,X11,X12,X13) = k2_enumset1(X13,X10,X12,X11) ),
    inference(forward_demodulation,[],[f1473,f35])).

fof(f1473,plain,(
    ! [X12,X10,X13,X11] : k3_enumset1(X10,X10,X11,X12,X13) = k3_enumset1(X13,X13,X10,X12,X11) ),
    inference(superposition,[],[f504,f436])).

fof(f436,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4) ),
    inference(forward_demodulation,[],[f432,f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f432,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4) ),
    inference(superposition,[],[f194,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f194,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k4_enumset1(X1,X2,X3,X4,X5,X0) ),
    inference(backward_demodulation,[],[f140,f193])).

fof(f193,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(forward_demodulation,[],[f188,f38])).

fof(f188,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(superposition,[],[f41,f36])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

fof(f140,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0)) ),
    inference(superposition,[],[f40,f27])).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

fof(f504,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X3,X4,X0,X2,X1) ),
    inference(forward_demodulation,[],[f480,f96])).

fof(f96,plain,(
    ! [X6,X8,X7,X5,X9] : k2_xboole_0(k1_enumset1(X7,X8,X9),k2_tarski(X5,X6)) = k3_enumset1(X5,X6,X7,X8,X9) ),
    inference(superposition,[],[f37,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(f480,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X2,X1),k2_tarski(X3,X4)) ),
    inference(superposition,[],[f145,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X2,X1) ),
    inference(superposition,[],[f34,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f145,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(forward_demodulation,[],[f139,f38])).

fof(f139,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(superposition,[],[f40,f35])).

fof(f26,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:50:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (27417)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (27428)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (27429)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (27425)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (27425)Refutation not found, incomplete strategy% (27425)------------------------------
% 0.20/0.47  % (27425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (27425)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (27425)Memory used [KB]: 10618
% 0.20/0.47  % (27425)Time elapsed: 0.052 s
% 0.20/0.47  % (27425)------------------------------
% 0.20/0.47  % (27425)------------------------------
% 0.20/0.47  % (27421)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (27416)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (27415)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (27418)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (27423)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (27427)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.49  % (27420)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (27414)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.49  % (27422)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (27426)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.50  % (27419)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.50  % (27430)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.50  % (27424)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.51  % (27431)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 2.33/0.68  % (27417)Refutation found. Thanks to Tanya!
% 2.33/0.68  % SZS status Theorem for theBenchmark
% 2.33/0.68  % SZS output start Proof for theBenchmark
% 2.33/0.68  fof(f8016,plain,(
% 2.33/0.68    $false),
% 2.33/0.68    inference(subsumption_resolution,[],[f7945,f149])).
% 2.33/0.68  fof(f149,plain,(
% 2.33/0.68    ( ! [X14,X17,X15,X16] : (k2_enumset1(X14,X15,X17,X16) = k2_enumset1(X14,X16,X17,X15)) )),
% 2.33/0.68    inference(superposition,[],[f56,f34])).
% 2.33/0.68  fof(f34,plain,(
% 2.33/0.68    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 2.33/0.68    inference(cnf_transformation,[],[f4])).
% 2.33/0.68  fof(f4,axiom,(
% 2.33/0.68    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 2.33/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).
% 2.33/0.68  fof(f56,plain,(
% 2.33/0.68    ( ! [X14,X12,X13,X11] : (k2_enumset1(X11,X13,X12,X14) = k2_enumset1(X11,X12,X14,X13)) )),
% 2.33/0.68    inference(superposition,[],[f34,f33])).
% 2.33/0.68  fof(f33,plain,(
% 2.33/0.68    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)) )),
% 2.33/0.68    inference(cnf_transformation,[],[f5])).
% 2.33/0.68  fof(f5,axiom,(
% 2.33/0.68    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 2.33/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).
% 2.33/0.68  fof(f7945,plain,(
% 2.33/0.68    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1)),
% 2.33/0.68    inference(superposition,[],[f26,f5039])).
% 2.33/0.68  fof(f5039,plain,(
% 2.33/0.68    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X6,X5)) )),
% 2.33/0.68    inference(superposition,[],[f1482,f35])).
% 2.33/0.68  fof(f35,plain,(
% 2.33/0.68    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.33/0.68    inference(cnf_transformation,[],[f17])).
% 2.33/0.68  fof(f17,axiom,(
% 2.33/0.68    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.33/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.33/0.68  fof(f1482,plain,(
% 2.33/0.68    ( ! [X12,X10,X13,X11] : (k3_enumset1(X10,X10,X11,X12,X13) = k2_enumset1(X13,X10,X12,X11)) )),
% 2.33/0.68    inference(forward_demodulation,[],[f1473,f35])).
% 2.33/0.68  fof(f1473,plain,(
% 2.33/0.68    ( ! [X12,X10,X13,X11] : (k3_enumset1(X10,X10,X11,X12,X13) = k3_enumset1(X13,X13,X10,X12,X11)) )),
% 2.33/0.68    inference(superposition,[],[f504,f436])).
% 2.33/0.68  fof(f436,plain,(
% 2.33/0.68    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)) )),
% 2.33/0.68    inference(forward_demodulation,[],[f432,f36])).
% 2.33/0.68  fof(f36,plain,(
% 2.33/0.68    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.33/0.68    inference(cnf_transformation,[],[f18])).
% 2.33/0.68  fof(f18,axiom,(
% 2.33/0.68    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.33/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.33/0.68  fof(f432,plain,(
% 2.33/0.68    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)) )),
% 2.33/0.68    inference(superposition,[],[f194,f38])).
% 2.33/0.68  fof(f38,plain,(
% 2.33/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.33/0.68    inference(cnf_transformation,[],[f19])).
% 2.33/0.68  fof(f19,axiom,(
% 2.33/0.68    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.33/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.33/0.68  fof(f194,plain,(
% 2.33/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k4_enumset1(X1,X2,X3,X4,X5,X0)) )),
% 2.33/0.68    inference(backward_demodulation,[],[f140,f193])).
% 2.33/0.68  fof(f193,plain,(
% 2.33/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 2.33/0.68    inference(forward_demodulation,[],[f188,f38])).
% 2.33/0.68  fof(f188,plain,(
% 2.33/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 2.33/0.68    inference(superposition,[],[f41,f36])).
% 2.33/0.68  fof(f41,plain,(
% 2.33/0.68    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 2.33/0.68    inference(cnf_transformation,[],[f8])).
% 2.33/0.68  fof(f8,axiom,(
% 2.33/0.68    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 2.33/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).
% 2.33/0.68  fof(f140,plain,(
% 2.33/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) )),
% 2.33/0.68    inference(superposition,[],[f40,f27])).
% 2.33/0.68  fof(f27,plain,(
% 2.33/0.68    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.33/0.68    inference(cnf_transformation,[],[f14])).
% 2.33/0.68  fof(f14,axiom,(
% 2.33/0.68    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.33/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.33/0.68  fof(f40,plain,(
% 2.33/0.68    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 2.33/0.68    inference(cnf_transformation,[],[f7])).
% 2.33/0.68  fof(f7,axiom,(
% 2.33/0.68    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 2.33/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).
% 2.33/0.68  fof(f504,plain,(
% 2.33/0.68    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X3,X4,X0,X2,X1)) )),
% 2.33/0.68    inference(forward_demodulation,[],[f480,f96])).
% 2.33/0.68  fof(f96,plain,(
% 2.33/0.68    ( ! [X6,X8,X7,X5,X9] : (k2_xboole_0(k1_enumset1(X7,X8,X9),k2_tarski(X5,X6)) = k3_enumset1(X5,X6,X7,X8,X9)) )),
% 2.33/0.68    inference(superposition,[],[f37,f28])).
% 2.33/0.68  fof(f28,plain,(
% 2.33/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.33/0.68    inference(cnf_transformation,[],[f1])).
% 2.33/0.68  fof(f1,axiom,(
% 2.33/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.33/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.33/0.68  fof(f37,plain,(
% 2.33/0.68    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 2.33/0.68    inference(cnf_transformation,[],[f6])).
% 2.33/0.68  fof(f6,axiom,(
% 2.33/0.68    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 2.33/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).
% 2.33/0.68  fof(f480,plain,(
% 2.33/0.68    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X2,X1),k2_tarski(X3,X4))) )),
% 2.33/0.68    inference(superposition,[],[f145,f55])).
% 2.33/0.68  fof(f55,plain,(
% 2.33/0.68    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X2,X1)) )),
% 2.33/0.68    inference(superposition,[],[f34,f32])).
% 2.33/0.68  fof(f32,plain,(
% 2.33/0.68    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.33/0.68    inference(cnf_transformation,[],[f16])).
% 2.33/0.68  fof(f16,axiom,(
% 2.33/0.68    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.33/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.33/0.68  fof(f145,plain,(
% 2.33/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 2.33/0.68    inference(forward_demodulation,[],[f139,f38])).
% 2.33/0.68  fof(f139,plain,(
% 2.33/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 2.33/0.68    inference(superposition,[],[f40,f35])).
% 2.33/0.68  fof(f26,plain,(
% 2.33/0.68    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 2.33/0.68    inference(cnf_transformation,[],[f25])).
% 2.33/0.68  fof(f25,plain,(
% 2.33/0.68    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 2.33/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f24])).
% 2.33/0.68  fof(f24,plain,(
% 2.33/0.68    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 2.33/0.68    introduced(choice_axiom,[])).
% 2.33/0.68  fof(f23,plain,(
% 2.33/0.68    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 2.33/0.68    inference(ennf_transformation,[],[f22])).
% 2.33/0.68  fof(f22,negated_conjecture,(
% 2.33/0.68    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 2.33/0.68    inference(negated_conjecture,[],[f21])).
% 2.33/0.68  fof(f21,conjecture,(
% 2.33/0.68    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 2.33/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).
% 2.33/0.68  % SZS output end Proof for theBenchmark
% 2.33/0.68  % (27417)------------------------------
% 2.33/0.68  % (27417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.33/0.68  % (27417)Termination reason: Refutation
% 2.33/0.68  
% 2.33/0.68  % (27417)Memory used [KB]: 10234
% 2.33/0.68  % (27417)Time elapsed: 0.264 s
% 2.33/0.68  % (27417)------------------------------
% 2.33/0.68  % (27417)------------------------------
% 2.33/0.68  % (27413)Success in time 0.323 s
%------------------------------------------------------------------------------
