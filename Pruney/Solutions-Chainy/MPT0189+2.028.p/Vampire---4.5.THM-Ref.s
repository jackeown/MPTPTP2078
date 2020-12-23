%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:21 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
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
fof(f2987,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2904,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

fof(f2904,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK1,sK2) ),
    inference(superposition,[],[f23,f1908])).

fof(f1908,plain,(
    ! [X47,X45,X46,X44] : k2_enumset1(X44,X46,X47,X45) = k2_enumset1(X46,X45,X44,X47) ),
    inference(superposition,[],[f1844,f31])).

fof(f1844,plain,(
    ! [X30,X28,X31,X29] : k2_enumset1(X28,X30,X29,X31) = k2_enumset1(X29,X30,X28,X31) ),
    inference(superposition,[],[f906,f589])).

fof(f589,plain,(
    ! [X43,X41,X42,X40] : k3_enumset1(X40,X41,X41,X42,X43) = k2_enumset1(X41,X42,X40,X43) ),
    inference(forward_demodulation,[],[f580,f350])).

fof(f350,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3)) ),
    inference(forward_demodulation,[],[f336,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f336,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3)) ),
    inference(superposition,[],[f331,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X2,X1) ),
    inference(superposition,[],[f30,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

fof(f331,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(forward_demodulation,[],[f330,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f330,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f177,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(superposition,[],[f36,f33])).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

fof(f580,plain,(
    ! [X43,X41,X42,X40] : k3_enumset1(X40,X41,X41,X42,X43) = k2_xboole_0(k1_enumset1(X41,X40,X42),k1_tarski(X43)) ),
    inference(superposition,[],[f331,f533])).

fof(f533,plain,(
    ! [X39,X38,X40] : k2_enumset1(X38,X39,X39,X40) = k1_enumset1(X39,X38,X40) ),
    inference(forward_demodulation,[],[f530,f531])).

fof(f531,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(forward_demodulation,[],[f520,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X2,X0,X1) = k1_enumset1(X0,X2,X1) ),
    inference(superposition,[],[f31,f55])).

fof(f520,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X1,X0,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(superposition,[],[f350,f25])).

fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f530,plain,(
    ! [X39,X38,X40] : k2_enumset1(X38,X39,X39,X40) = k2_xboole_0(k2_tarski(X39,X38),k1_tarski(X40)) ),
    inference(superposition,[],[f350,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0) ),
    inference(superposition,[],[f28,f25])).

fof(f28,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

fof(f906,plain,(
    ! [X50,X48,X51,X49] : k2_enumset1(X48,X50,X49,X51) = k3_enumset1(X48,X49,X49,X50,X51) ),
    inference(forward_demodulation,[],[f897,f350])).

fof(f897,plain,(
    ! [X50,X48,X51,X49] : k3_enumset1(X48,X49,X49,X50,X51) = k2_xboole_0(k1_enumset1(X48,X49,X50),k1_tarski(X51)) ),
    inference(superposition,[],[f331,f648])).

fof(f648,plain,(
    ! [X66,X64,X65] : k2_enumset1(X64,X65,X65,X66) = k1_enumset1(X64,X65,X66) ),
    inference(forward_demodulation,[],[f640,f531])).

fof(f640,plain,(
    ! [X66,X64,X65] : k2_enumset1(X64,X65,X65,X66) = k2_xboole_0(k2_tarski(X64,X65),k1_tarski(X66)) ),
    inference(superposition,[],[f350,f585])).

fof(f585,plain,(
    ! [X28,X29] : k1_enumset1(X28,X29,X29) = k2_tarski(X28,X29) ),
    inference(forward_demodulation,[],[f568,f43])).

fof(f568,plain,(
    ! [X28,X29] : k1_enumset1(X28,X29,X29) = k1_enumset1(X29,X28,X28) ),
    inference(superposition,[],[f533,f65])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:51:59 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.40  % (19374)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.18/0.46  % (19380)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.18/0.49  % (19367)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.18/0.50  % (19370)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.18/0.50  % (19376)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.18/0.51  % (19368)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.18/0.51  % (19378)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.18/0.51  % (19378)Refutation not found, incomplete strategy% (19378)------------------------------
% 0.18/0.51  % (19378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (19378)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.51  
% 0.18/0.51  % (19378)Memory used [KB]: 10618
% 0.18/0.51  % (19378)Time elapsed: 0.074 s
% 0.18/0.51  % (19378)------------------------------
% 0.18/0.51  % (19378)------------------------------
% 0.18/0.52  % (19384)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.18/0.52  % (19371)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.18/0.52  % (19372)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.18/0.52  % (19375)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.18/0.53  % (19381)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.18/0.53  % (19369)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.18/0.54  % (19373)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.18/0.54  % (19379)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.18/0.55  % (19383)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.18/0.55  % (19377)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.18/0.56  % (19382)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.18/0.62  % (19370)Refutation found. Thanks to Tanya!
% 0.18/0.62  % SZS status Theorem for theBenchmark
% 0.18/0.62  % SZS output start Proof for theBenchmark
% 0.18/0.62  fof(f2987,plain,(
% 0.18/0.62    $false),
% 0.18/0.62    inference(subsumption_resolution,[],[f2904,f31])).
% 0.18/0.62  fof(f31,plain,(
% 0.18/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 0.18/0.62    inference(cnf_transformation,[],[f5])).
% 0.18/0.62  fof(f5,axiom,(
% 0.18/0.62    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.18/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).
% 0.18/0.62  fof(f2904,plain,(
% 0.18/0.62    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK1,sK2)),
% 0.18/0.62    inference(superposition,[],[f23,f1908])).
% 0.18/0.62  fof(f1908,plain,(
% 0.18/0.62    ( ! [X47,X45,X46,X44] : (k2_enumset1(X44,X46,X47,X45) = k2_enumset1(X46,X45,X44,X47)) )),
% 0.18/0.62    inference(superposition,[],[f1844,f31])).
% 0.18/0.62  fof(f1844,plain,(
% 0.18/0.62    ( ! [X30,X28,X31,X29] : (k2_enumset1(X28,X30,X29,X31) = k2_enumset1(X29,X30,X28,X31)) )),
% 0.18/0.62    inference(superposition,[],[f906,f589])).
% 0.18/0.62  fof(f589,plain,(
% 0.18/0.62    ( ! [X43,X41,X42,X40] : (k3_enumset1(X40,X41,X41,X42,X43) = k2_enumset1(X41,X42,X40,X43)) )),
% 0.18/0.62    inference(forward_demodulation,[],[f580,f350])).
% 0.18/0.62  fof(f350,plain,(
% 0.18/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3))) )),
% 0.18/0.62    inference(forward_demodulation,[],[f336,f32])).
% 0.18/0.62  fof(f32,plain,(
% 0.18/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.18/0.62    inference(cnf_transformation,[],[f14])).
% 0.18/0.62  fof(f14,axiom,(
% 0.18/0.62    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.18/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.18/0.62  fof(f336,plain,(
% 0.18/0.62    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3))) )),
% 0.18/0.62    inference(superposition,[],[f331,f55])).
% 0.18/0.62  fof(f55,plain,(
% 0.18/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X2,X1)) )),
% 0.18/0.62    inference(superposition,[],[f30,f29])).
% 0.18/0.62  fof(f29,plain,(
% 0.18/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.18/0.62    inference(cnf_transformation,[],[f13])).
% 0.18/0.62  fof(f13,axiom,(
% 0.18/0.62    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.18/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.18/0.62  fof(f30,plain,(
% 0.18/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 0.18/0.62    inference(cnf_transformation,[],[f4])).
% 0.18/0.62  fof(f4,axiom,(
% 0.18/0.62    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 0.18/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).
% 0.18/0.62  fof(f331,plain,(
% 0.18/0.62    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.18/0.62    inference(forward_demodulation,[],[f330,f33])).
% 0.18/0.62  fof(f33,plain,(
% 0.18/0.62    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.18/0.62    inference(cnf_transformation,[],[f15])).
% 0.18/0.62  fof(f15,axiom,(
% 0.18/0.62    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.18/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.18/0.62  fof(f330,plain,(
% 0.18/0.62    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.18/0.62    inference(superposition,[],[f178,f32])).
% 0.18/0.62  fof(f178,plain,(
% 0.18/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.18/0.62    inference(forward_demodulation,[],[f177,f34])).
% 0.18/0.63  fof(f34,plain,(
% 0.18/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.18/0.63    inference(cnf_transformation,[],[f16])).
% 0.18/0.63  fof(f16,axiom,(
% 0.18/0.63    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.18/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.18/0.63  fof(f177,plain,(
% 0.18/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.18/0.63    inference(superposition,[],[f36,f33])).
% 0.18/0.63  fof(f36,plain,(
% 0.18/0.63    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 0.18/0.63    inference(cnf_transformation,[],[f6])).
% 0.18/0.63  fof(f6,axiom,(
% 0.18/0.63    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 0.18/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).
% 0.18/0.63  fof(f580,plain,(
% 0.18/0.63    ( ! [X43,X41,X42,X40] : (k3_enumset1(X40,X41,X41,X42,X43) = k2_xboole_0(k1_enumset1(X41,X40,X42),k1_tarski(X43))) )),
% 0.18/0.63    inference(superposition,[],[f331,f533])).
% 0.18/0.63  fof(f533,plain,(
% 0.18/0.63    ( ! [X39,X38,X40] : (k2_enumset1(X38,X39,X39,X40) = k1_enumset1(X39,X38,X40)) )),
% 0.18/0.63    inference(forward_demodulation,[],[f530,f531])).
% 0.18/0.63  fof(f531,plain,(
% 0.18/0.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.18/0.63    inference(forward_demodulation,[],[f520,f70])).
% 0.18/0.63  fof(f70,plain,(
% 0.18/0.63    ( ! [X2,X0,X1] : (k2_enumset1(X0,X2,X0,X1) = k1_enumset1(X0,X2,X1)) )),
% 0.18/0.63    inference(superposition,[],[f31,f55])).
% 0.18/0.63  fof(f520,plain,(
% 0.18/0.63    ( ! [X2,X0,X1] : (k2_enumset1(X0,X1,X0,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.18/0.63    inference(superposition,[],[f350,f25])).
% 0.18/0.63  fof(f25,plain,(
% 0.18/0.63    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.18/0.63    inference(cnf_transformation,[],[f12])).
% 0.18/0.63  fof(f12,axiom,(
% 0.18/0.63    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.18/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.18/0.63  fof(f530,plain,(
% 0.18/0.63    ( ! [X39,X38,X40] : (k2_enumset1(X38,X39,X39,X40) = k2_xboole_0(k2_tarski(X39,X38),k1_tarski(X40))) )),
% 0.18/0.63    inference(superposition,[],[f350,f43])).
% 0.18/0.63  fof(f43,plain,(
% 0.18/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)) )),
% 0.18/0.63    inference(superposition,[],[f28,f25])).
% 0.18/0.63  fof(f28,plain,(
% 0.18/0.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 0.18/0.63    inference(cnf_transformation,[],[f3])).
% 0.18/0.63  fof(f3,axiom,(
% 0.18/0.63    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 0.18/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).
% 0.18/0.63  fof(f906,plain,(
% 0.18/0.63    ( ! [X50,X48,X51,X49] : (k2_enumset1(X48,X50,X49,X51) = k3_enumset1(X48,X49,X49,X50,X51)) )),
% 0.18/0.63    inference(forward_demodulation,[],[f897,f350])).
% 0.18/0.63  fof(f897,plain,(
% 0.18/0.63    ( ! [X50,X48,X51,X49] : (k3_enumset1(X48,X49,X49,X50,X51) = k2_xboole_0(k1_enumset1(X48,X49,X50),k1_tarski(X51))) )),
% 0.18/0.63    inference(superposition,[],[f331,f648])).
% 0.18/0.63  fof(f648,plain,(
% 0.18/0.63    ( ! [X66,X64,X65] : (k2_enumset1(X64,X65,X65,X66) = k1_enumset1(X64,X65,X66)) )),
% 0.18/0.63    inference(forward_demodulation,[],[f640,f531])).
% 0.18/0.63  fof(f640,plain,(
% 0.18/0.63    ( ! [X66,X64,X65] : (k2_enumset1(X64,X65,X65,X66) = k2_xboole_0(k2_tarski(X64,X65),k1_tarski(X66))) )),
% 0.18/0.63    inference(superposition,[],[f350,f585])).
% 0.18/0.63  fof(f585,plain,(
% 0.18/0.63    ( ! [X28,X29] : (k1_enumset1(X28,X29,X29) = k2_tarski(X28,X29)) )),
% 0.18/0.63    inference(forward_demodulation,[],[f568,f43])).
% 0.18/0.63  fof(f568,plain,(
% 0.18/0.63    ( ! [X28,X29] : (k1_enumset1(X28,X29,X29) = k1_enumset1(X29,X28,X28)) )),
% 0.18/0.63    inference(superposition,[],[f533,f65])).
% 0.18/0.63  fof(f65,plain,(
% 0.18/0.63    ( ! [X2,X0,X1] : (k2_enumset1(X0,X1,X2,X0) = k1_enumset1(X0,X2,X1)) )),
% 0.18/0.63    inference(superposition,[],[f31,f55])).
% 0.18/0.63  fof(f23,plain,(
% 0.18/0.63    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 0.18/0.63    inference(cnf_transformation,[],[f22])).
% 0.18/0.63  fof(f22,plain,(
% 0.18/0.63    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 0.18/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f21])).
% 0.18/0.63  fof(f21,plain,(
% 0.18/0.63    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 0.18/0.63    introduced(choice_axiom,[])).
% 0.18/0.63  fof(f20,plain,(
% 0.18/0.63    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 0.18/0.63    inference(ennf_transformation,[],[f19])).
% 0.18/0.63  fof(f19,negated_conjecture,(
% 0.18/0.63    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 0.18/0.63    inference(negated_conjecture,[],[f18])).
% 0.18/0.63  fof(f18,conjecture,(
% 0.18/0.63    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 0.18/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).
% 0.18/0.63  % SZS output end Proof for theBenchmark
% 0.18/0.63  % (19370)------------------------------
% 0.18/0.63  % (19370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.63  % (19370)Termination reason: Refutation
% 0.18/0.63  
% 0.18/0.63  % (19370)Memory used [KB]: 4733
% 0.18/0.63  % (19370)Time elapsed: 0.183 s
% 0.18/0.63  % (19370)------------------------------
% 0.18/0.63  % (19370)------------------------------
% 0.18/0.63  % (19366)Success in time 0.284 s
%------------------------------------------------------------------------------
