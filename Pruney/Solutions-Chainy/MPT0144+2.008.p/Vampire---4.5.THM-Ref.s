%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  58 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :   38 (  59 expanded)
%              Number of equality atoms :   37 (  58 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2073,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f2061])).

fof(f2061,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) ),
    inference(superposition,[],[f16,f751])).

fof(f751,plain,(
    ! [X6,X12,X10,X8,X7,X11,X9] : k2_xboole_0(k3_enumset1(X11,X12,X6,X7,X8),k2_tarski(X9,X10)) = k5_enumset1(X11,X12,X6,X7,X8,X9,X10) ),
    inference(forward_demodulation,[],[f738,f183])).

fof(f183,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X5,X6),k3_enumset1(X0,X1,X2,X3,X4)) = k5_enumset1(X5,X6,X0,X1,X2,X3,X4) ),
    inference(forward_demodulation,[],[f180,f26])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

fof(f180,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_enumset1(X5,X6,X0,X1),k1_enumset1(X2,X3,X4)) = k2_xboole_0(k2_tarski(X5,X6),k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(superposition,[],[f42,f71])).

fof(f71,plain,(
    ! [X14,X17,X15,X18,X16] : k2_xboole_0(k2_tarski(X18,X14),k1_enumset1(X15,X16,X17)) = k3_enumset1(X18,X14,X15,X16,X17) ),
    inference(forward_demodulation,[],[f66,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(f66,plain,(
    ! [X14,X17,X15,X18,X16] : k2_xboole_0(k2_tarski(X18,X14),k1_enumset1(X15,X16,X17)) = k2_xboole_0(k1_tarski(X18),k2_enumset1(X14,X15,X16,X17)) ),
    inference(superposition,[],[f36,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(superposition,[],[f22,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),X4) = k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k2_tarski(X2,X3),X4)) ),
    inference(superposition,[],[f22,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f738,plain,(
    ! [X6,X12,X10,X8,X7,X11,X9] : k2_xboole_0(k3_enumset1(X11,X12,X6,X7,X8),k2_tarski(X9,X10)) = k2_xboole_0(k2_tarski(X11,X12),k3_enumset1(X6,X7,X8,X9,X10)) ),
    inference(superposition,[],[f148,f138])).

fof(f138,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X4,X0,X1),k2_tarski(X2,X3)) = k3_enumset1(X4,X0,X1,X2,X3) ),
    inference(forward_demodulation,[],[f134,f25])).

fof(f134,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X4,X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3)) ),
    inference(superposition,[],[f37,f24])).

fof(f37,plain,(
    ! [X6,X4,X5,X3] : k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6) ),
    inference(superposition,[],[f22,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f148,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X5,X0),k2_xboole_0(k1_enumset1(X1,X2,X3),X4)) = k2_xboole_0(k3_enumset1(X5,X0,X1,X2,X3),X4) ),
    inference(forward_demodulation,[],[f145,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_enumset1(X1,X2,X3,X4),X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),X5) ),
    inference(superposition,[],[f22,f25])).

fof(f145,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X5,X0),k2_xboole_0(k1_enumset1(X1,X2,X3),X4)) = k2_xboole_0(k1_tarski(X5),k2_xboole_0(k2_enumset1(X0,X1,X2,X3),X4)) ),
    inference(superposition,[],[f36,f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_enumset1(X1,X2,X3),X4)) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),X4) ),
    inference(superposition,[],[f22,f23])).

fof(f16,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:40:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (1268)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (1267)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (1260)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (1267)Refutation not found, incomplete strategy% (1267)------------------------------
% 0.21/0.47  % (1267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (1267)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (1267)Memory used [KB]: 10618
% 0.21/0.47  % (1267)Time elapsed: 0.051 s
% 0.21/0.47  % (1267)------------------------------
% 0.21/0.47  % (1267)------------------------------
% 0.21/0.47  % (1261)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (1259)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (1257)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (1273)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (1271)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (1269)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (1266)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (1265)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (1256)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (1272)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (1263)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (1262)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (1258)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (1264)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (1270)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.53  % (1259)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f2073,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f2061])).
% 0.21/0.53  fof(f2061,plain,(
% 0.21/0.53    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6)),
% 0.21/0.53    inference(superposition,[],[f16,f751])).
% 0.21/0.53  fof(f751,plain,(
% 0.21/0.53    ( ! [X6,X12,X10,X8,X7,X11,X9] : (k2_xboole_0(k3_enumset1(X11,X12,X6,X7,X8),k2_tarski(X9,X10)) = k5_enumset1(X11,X12,X6,X7,X8,X9,X10)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f738,f183])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X5,X6),k3_enumset1(X0,X1,X2,X3,X4)) = k5_enumset1(X5,X6,X0,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f180,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X5,X6,X0,X1),k1_enumset1(X2,X3,X4)) = k2_xboole_0(k2_tarski(X5,X6),k3_enumset1(X0,X1,X2,X3,X4))) )),
% 0.21/0.53    inference(superposition,[],[f42,f71])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X14,X17,X15,X18,X16] : (k2_xboole_0(k2_tarski(X18,X14),k1_enumset1(X15,X16,X17)) = k3_enumset1(X18,X14,X15,X16,X17)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f66,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X14,X17,X15,X18,X16] : (k2_xboole_0(k2_tarski(X18,X14),k1_enumset1(X15,X16,X17)) = k2_xboole_0(k1_tarski(X18),k2_enumset1(X14,X15,X16,X17))) )),
% 0.21/0.53    inference(superposition,[],[f36,f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.21/0.53    inference(superposition,[],[f22,f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),X4) = k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k2_tarski(X2,X3),X4))) )),
% 0.21/0.53    inference(superposition,[],[f22,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 0.21/0.53  fof(f738,plain,(
% 0.21/0.53    ( ! [X6,X12,X10,X8,X7,X11,X9] : (k2_xboole_0(k3_enumset1(X11,X12,X6,X7,X8),k2_tarski(X9,X10)) = k2_xboole_0(k2_tarski(X11,X12),k3_enumset1(X6,X7,X8,X9,X10))) )),
% 0.21/0.53    inference(superposition,[],[f148,f138])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X4,X0,X1),k2_tarski(X2,X3)) = k3_enumset1(X4,X0,X1,X2,X3)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f134,f25])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X4,X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3))) )),
% 0.21/0.53    inference(superposition,[],[f37,f24])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X6,X4,X5,X3] : (k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) )),
% 0.21/0.53    inference(superposition,[],[f22,f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X5,X0),k2_xboole_0(k1_enumset1(X1,X2,X3),X4)) = k2_xboole_0(k3_enumset1(X5,X0,X1,X2,X3),X4)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f145,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_enumset1(X1,X2,X3,X4),X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),X5)) )),
% 0.21/0.53    inference(superposition,[],[f22,f25])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X5,X0),k2_xboole_0(k1_enumset1(X1,X2,X3),X4)) = k2_xboole_0(k1_tarski(X5),k2_xboole_0(k2_enumset1(X0,X1,X2,X3),X4))) )),
% 0.21/0.53    inference(superposition,[],[f36,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_enumset1(X1,X2,X3),X4)) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),X4)) )),
% 0.21/0.53    inference(superposition,[],[f22,f23])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f13,f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.21/0.53    inference(negated_conjecture,[],[f11])).
% 0.21/0.53  fof(f11,conjecture,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (1259)------------------------------
% 0.21/0.53  % (1259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1259)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (1259)Memory used [KB]: 4861
% 0.21/0.53  % (1259)Time elapsed: 0.118 s
% 0.21/0.53  % (1259)------------------------------
% 0.21/0.53  % (1259)------------------------------
% 0.21/0.53  % (1255)Success in time 0.172 s
%------------------------------------------------------------------------------
