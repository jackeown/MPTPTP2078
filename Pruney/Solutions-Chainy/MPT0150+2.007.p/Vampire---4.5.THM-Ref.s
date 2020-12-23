%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 (  99 expanded)
%              Number of leaves         :    8 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :   40 ( 100 expanded)
%              Number of equality atoms :   39 (  99 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f727,plain,(
    $false ),
    inference(subsumption_resolution,[],[f16,f726])).

fof(f726,plain,(
    ! [X26,X24,X23,X21,X27,X25,X22,X20] : k2_xboole_0(k3_enumset1(X26,X27,X20,X21,X22),k1_enumset1(X23,X24,X25)) = k6_enumset1(X26,X27,X20,X21,X22,X23,X24,X25) ),
    inference(forward_demodulation,[],[f725,f489])).

fof(f489,plain,(
    ! [X28,X26,X24,X23,X21,X27,X25,X22] : k2_xboole_0(k1_enumset1(X26,X27,X28),k3_enumset1(X21,X22,X23,X24,X25)) = k6_enumset1(X26,X27,X28,X21,X22,X23,X24,X25) ),
    inference(forward_demodulation,[],[f474,f26])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(f474,plain,(
    ! [X28,X26,X24,X23,X21,X27,X25,X22] : k2_xboole_0(k2_enumset1(X26,X27,X28,X21),k2_enumset1(X22,X23,X24,X25)) = k2_xboole_0(k1_enumset1(X26,X27,X28),k3_enumset1(X21,X22,X23,X24,X25)) ),
    inference(superposition,[],[f142,f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f142,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_tarski(X3),X4)) ),
    inference(superposition,[],[f22,f137])).

fof(f137,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X3,X0,X1),k1_tarski(X2)) = k2_enumset1(X3,X0,X1,X2) ),
    inference(forward_demodulation,[],[f133,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f133,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X3,X0,X1),k1_tarski(X2)) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f37,f67])).

fof(f67,plain,(
    ! [X10,X8,X9] : k2_xboole_0(k2_tarski(X10,X8),k1_tarski(X9)) = k1_enumset1(X10,X8,X9) ),
    inference(forward_demodulation,[],[f62,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f62,plain,(
    ! [X10,X8,X9] : k2_xboole_0(k2_tarski(X10,X8),k1_tarski(X9)) = k2_xboole_0(k1_tarski(X10),k2_tarski(X8,X9)) ),
    inference(superposition,[],[f36,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(superposition,[],[f22,f17])).

fof(f37,plain,(
    ! [X6,X4,X5,X3] : k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6) ),
    inference(superposition,[],[f22,f20])).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f725,plain,(
    ! [X26,X24,X23,X21,X27,X25,X22,X20] : k2_xboole_0(k3_enumset1(X26,X27,X20,X21,X22),k1_enumset1(X23,X24,X25)) = k2_xboole_0(k1_enumset1(X26,X27,X20),k3_enumset1(X21,X22,X23,X24,X25)) ),
    inference(forward_demodulation,[],[f712,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_enumset1(X3,X0,X1),X2) ),
    inference(forward_demodulation,[],[f60,f37])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X0,X1),X2)) ),
    inference(superposition,[],[f36,f36])).

fof(f712,plain,(
    ! [X26,X24,X23,X21,X27,X25,X22,X20] : k2_xboole_0(k3_enumset1(X26,X27,X20,X21,X22),k1_enumset1(X23,X24,X25)) = k2_xboole_0(k2_tarski(X26,X27),k2_xboole_0(k1_tarski(X20),k3_enumset1(X21,X22,X23,X24,X25))) ),
    inference(superposition,[],[f159,f154])).

fof(f154,plain,(
    ! [X30,X28,X31,X29,X27,X32] : k2_xboole_0(k1_enumset1(X31,X32,X27),k1_enumset1(X28,X29,X30)) = k2_xboole_0(k1_tarski(X31),k3_enumset1(X32,X27,X28,X29,X30)) ),
    inference(forward_demodulation,[],[f148,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X5,X0),k2_enumset1(X1,X2,X3,X4)) = k2_xboole_0(k1_tarski(X5),k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(superposition,[],[f36,f24])).

fof(f148,plain,(
    ! [X30,X28,X31,X29,X27,X32] : k2_xboole_0(k1_enumset1(X31,X32,X27),k1_enumset1(X28,X29,X30)) = k2_xboole_0(k2_tarski(X31,X32),k2_enumset1(X27,X28,X29,X30)) ),
    inference(superposition,[],[f65,f23])).

fof(f159,plain,(
    ! [X6,X10,X8,X7,X11,X9] : k2_xboole_0(k3_enumset1(X6,X7,X8,X9,X10),X11) = k2_xboole_0(k2_tarski(X6,X7),k2_xboole_0(k1_enumset1(X8,X9,X10),X11)) ),
    inference(superposition,[],[f22,f68])).

fof(f68,plain,(
    ! [X14,X12,X15,X13,X11] : k2_xboole_0(k2_tarski(X15,X11),k1_enumset1(X12,X13,X14)) = k3_enumset1(X15,X11,X12,X13,X14) ),
    inference(forward_demodulation,[],[f63,f24])).

fof(f63,plain,(
    ! [X14,X12,X15,X13,X11] : k2_xboole_0(k2_tarski(X15,X11),k1_enumset1(X12,X13,X14)) = k2_xboole_0(k1_tarski(X15),k2_enumset1(X11,X12,X13,X14)) ),
    inference(superposition,[],[f36,f23])).

fof(f16,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_enumset1(sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_enumset1(sK5,sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_enumset1(sK5,sK6,sK7)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (30365)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (30372)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (30366)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (30364)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (30367)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (30369)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (30380)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.48  % (30363)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (30368)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (30374)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (30375)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (30374)Refutation not found, incomplete strategy% (30374)------------------------------
% 0.20/0.48  % (30374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (30374)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (30374)Memory used [KB]: 10618
% 0.20/0.48  % (30374)Time elapsed: 0.038 s
% 0.20/0.48  % (30374)------------------------------
% 0.20/0.48  % (30374)------------------------------
% 0.20/0.48  % (30378)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.49  % (30370)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (30377)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (30376)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.50  % (30371)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.50  % (30362)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.51  % (30379)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.55  % (30379)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f727,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(subsumption_resolution,[],[f16,f726])).
% 0.20/0.55  fof(f726,plain,(
% 0.20/0.55    ( ! [X26,X24,X23,X21,X27,X25,X22,X20] : (k2_xboole_0(k3_enumset1(X26,X27,X20,X21,X22),k1_enumset1(X23,X24,X25)) = k6_enumset1(X26,X27,X20,X21,X22,X23,X24,X25)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f725,f489])).
% 0.20/0.55  fof(f489,plain,(
% 0.20/0.55    ( ! [X28,X26,X24,X23,X21,X27,X25,X22] : (k2_xboole_0(k1_enumset1(X26,X27,X28),k3_enumset1(X21,X22,X23,X24,X25)) = k6_enumset1(X26,X27,X28,X21,X22,X23,X24,X25)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f474,f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).
% 0.20/0.55  fof(f474,plain,(
% 0.20/0.55    ( ! [X28,X26,X24,X23,X21,X27,X25,X22] : (k2_xboole_0(k2_enumset1(X26,X27,X28,X21),k2_enumset1(X22,X23,X24,X25)) = k2_xboole_0(k1_enumset1(X26,X27,X28),k3_enumset1(X21,X22,X23,X24,X25))) )),
% 0.20/0.55    inference(superposition,[],[f142,f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 0.20/0.55  fof(f142,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_tarski(X3),X4))) )),
% 0.20/0.55    inference(superposition,[],[f22,f137])).
% 0.20/0.55  fof(f137,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X3,X0,X1),k1_tarski(X2)) = k2_enumset1(X3,X0,X1,X2)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f133,f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.20/0.55  fof(f133,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X3,X0,X1),k1_tarski(X2)) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2))) )),
% 0.20/0.55    inference(superposition,[],[f37,f67])).
% 0.20/0.55  fof(f67,plain,(
% 0.20/0.55    ( ! [X10,X8,X9] : (k2_xboole_0(k2_tarski(X10,X8),k1_tarski(X9)) = k1_enumset1(X10,X8,X9)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f62,f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    ( ! [X10,X8,X9] : (k2_xboole_0(k2_tarski(X10,X8),k1_tarski(X9)) = k2_xboole_0(k1_tarski(X10),k2_tarski(X8,X9))) )),
% 0.20/0.55    inference(superposition,[],[f36,f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.20/0.55    inference(superposition,[],[f22,f17])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ( ! [X6,X4,X5,X3] : (k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) )),
% 0.20/0.55    inference(superposition,[],[f22,f20])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.20/0.55  fof(f725,plain,(
% 0.20/0.55    ( ! [X26,X24,X23,X21,X27,X25,X22,X20] : (k2_xboole_0(k3_enumset1(X26,X27,X20,X21,X22),k1_enumset1(X23,X24,X25)) = k2_xboole_0(k1_enumset1(X26,X27,X20),k3_enumset1(X21,X22,X23,X24,X25))) )),
% 0.20/0.55    inference(forward_demodulation,[],[f712,f65])).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_enumset1(X3,X0,X1),X2)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f60,f37])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X0,X1),X2))) )),
% 0.20/0.55    inference(superposition,[],[f36,f36])).
% 0.20/0.55  fof(f712,plain,(
% 0.20/0.55    ( ! [X26,X24,X23,X21,X27,X25,X22,X20] : (k2_xboole_0(k3_enumset1(X26,X27,X20,X21,X22),k1_enumset1(X23,X24,X25)) = k2_xboole_0(k2_tarski(X26,X27),k2_xboole_0(k1_tarski(X20),k3_enumset1(X21,X22,X23,X24,X25)))) )),
% 0.20/0.55    inference(superposition,[],[f159,f154])).
% 0.20/0.55  fof(f154,plain,(
% 0.20/0.55    ( ! [X30,X28,X31,X29,X27,X32] : (k2_xboole_0(k1_enumset1(X31,X32,X27),k1_enumset1(X28,X29,X30)) = k2_xboole_0(k1_tarski(X31),k3_enumset1(X32,X27,X28,X29,X30))) )),
% 0.20/0.55    inference(forward_demodulation,[],[f148,f73])).
% 0.20/0.55  fof(f73,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X5,X0),k2_enumset1(X1,X2,X3,X4)) = k2_xboole_0(k1_tarski(X5),k3_enumset1(X0,X1,X2,X3,X4))) )),
% 0.20/0.55    inference(superposition,[],[f36,f24])).
% 0.20/0.55  fof(f148,plain,(
% 0.20/0.55    ( ! [X30,X28,X31,X29,X27,X32] : (k2_xboole_0(k1_enumset1(X31,X32,X27),k1_enumset1(X28,X29,X30)) = k2_xboole_0(k2_tarski(X31,X32),k2_enumset1(X27,X28,X29,X30))) )),
% 0.20/0.55    inference(superposition,[],[f65,f23])).
% 0.20/0.55  fof(f159,plain,(
% 0.20/0.55    ( ! [X6,X10,X8,X7,X11,X9] : (k2_xboole_0(k3_enumset1(X6,X7,X8,X9,X10),X11) = k2_xboole_0(k2_tarski(X6,X7),k2_xboole_0(k1_enumset1(X8,X9,X10),X11))) )),
% 0.20/0.55    inference(superposition,[],[f22,f68])).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    ( ! [X14,X12,X15,X13,X11] : (k2_xboole_0(k2_tarski(X15,X11),k1_enumset1(X12,X13,X14)) = k3_enumset1(X15,X11,X12,X13,X14)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f63,f24])).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    ( ! [X14,X12,X15,X13,X11] : (k2_xboole_0(k2_tarski(X15,X11),k1_enumset1(X12,X13,X14)) = k2_xboole_0(k1_tarski(X15),k2_enumset1(X11,X12,X13,X14))) )),
% 0.20/0.55    inference(superposition,[],[f36,f23])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_enumset1(sK5,sK6,sK7))),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_enumset1(sK5,sK6,sK7))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f13,f14])).
% 0.20/0.55  fof(f14,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_enumset1(sK5,sK6,sK7))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f13,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))),
% 0.20/0.55    inference(ennf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))),
% 0.20/0.55    inference(negated_conjecture,[],[f11])).
% 0.20/0.55  fof(f11,conjecture,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (30379)------------------------------
% 0.20/0.55  % (30379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (30379)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (30379)Memory used [KB]: 7419
% 0.20/0.55  % (30379)Time elapsed: 0.136 s
% 0.20/0.55  % (30379)------------------------------
% 0.20/0.55  % (30379)------------------------------
% 0.20/0.55  % (30356)Success in time 0.196 s
%------------------------------------------------------------------------------
