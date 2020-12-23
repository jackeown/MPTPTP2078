%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:22 EST 2020

% Result     : Theorem 2.53s
% Output     : Refutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 153 expanded)
%              Number of leaves         :   12 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :   54 ( 154 expanded)
%              Number of equality atoms :   53 ( 153 expanded)
%              Maximal formula depth    :    9 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5812,plain,(
    $false ),
    inference(subsumption_resolution,[],[f22,f5760])).

fof(f5760,plain,(
    ! [X54,X52,X55,X53] : k2_enumset1(X52,X54,X53,X55) = k2_enumset1(X54,X52,X53,X55) ),
    inference(superposition,[],[f5147,f3445])).

fof(f3445,plain,(
    ! [X54,X52,X55,X53] : k2_enumset1(X52,X53,X54,X55) = k3_enumset1(X52,X54,X53,X54,X55) ),
    inference(forward_demodulation,[],[f3381,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X0,X2,X3) ),
    inference(forward_demodulation,[],[f85,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f85,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X1,X0,X2,X3) ),
    inference(superposition,[],[f83,f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f83,plain,(
    ! [X21,X19,X17,X20,X18] : k4_enumset1(X17,X18,X19,X17,X20,X21) = k3_enumset1(X17,X18,X19,X20,X21) ),
    inference(forward_demodulation,[],[f79,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f76,f31])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(superposition,[],[f75,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(forward_demodulation,[],[f73,f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(superposition,[],[f34,f30])).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

fof(f79,plain,(
    ! [X21,X19,X17,X20,X18] : k4_enumset1(X17,X18,X19,X17,X20,X21) = k2_xboole_0(k1_enumset1(X17,X18,X19),k2_tarski(X20,X21)) ),
    inference(superposition,[],[f75,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X0) ),
    inference(superposition,[],[f29,f28])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

fof(f3381,plain,(
    ! [X54,X52,X55,X53] : k3_enumset1(X52,X54,X53,X54,X55) = k3_enumset1(X52,X53,X52,X54,X55) ),
    inference(superposition,[],[f2805,f84])).

fof(f84,plain,(
    ! [X26,X24,X23,X25,X22] : k4_enumset1(X22,X23,X22,X24,X25,X26) = k3_enumset1(X22,X24,X23,X25,X26) ),
    inference(forward_demodulation,[],[f80,f82])).

fof(f80,plain,(
    ! [X26,X24,X23,X25,X22] : k4_enumset1(X22,X23,X22,X24,X25,X26) = k2_xboole_0(k1_enumset1(X22,X24,X23),k2_tarski(X25,X26)) ),
    inference(superposition,[],[f75,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X0,X1) ),
    inference(superposition,[],[f29,f28])).

fof(f2805,plain,(
    ! [X68,X66,X69,X67,X65] : k4_enumset1(X65,X66,X67,X68,X68,X69) = k3_enumset1(X65,X66,X67,X68,X69) ),
    inference(forward_demodulation,[],[f2749,f31])).

fof(f2749,plain,(
    ! [X68,X66,X69,X67,X65] : k4_enumset1(X65,X66,X67,X68,X68,X69) = k4_enumset1(X65,X65,X66,X67,X68,X69) ),
    inference(superposition,[],[f2721,f32])).

fof(f2721,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X3,X4,X4,X5) ),
    inference(forward_demodulation,[],[f2715,f32])).

fof(f2715,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X3,X4,X4,X5) ),
    inference(superposition,[],[f2651,f33])).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f2651,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X2,X3,X4,X5,X6,X0,X0,X1) = k5_enumset1(X2,X3,X4,X5,X6,X0,X1) ),
    inference(forward_demodulation,[],[f2643,f34])).

fof(f2643,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X2,X3,X4,X5,X6,X0,X0,X1) = k2_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f36,f24])).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).

fof(f5147,plain,(
    ! [X70,X72,X71,X73] : k2_enumset1(X70,X71,X72,X73) = k3_enumset1(X71,X72,X70,X72,X73) ),
    inference(superposition,[],[f3432,f494])).

fof(f494,plain,(
    ! [X6,X8,X7,X5,X9] : k3_enumset1(X5,X6,X7,X8,X9) = k3_enumset1(X6,X7,X5,X8,X9) ),
    inference(superposition,[],[f100,f82])).

fof(f100,plain,(
    ! [X6,X4,X8,X7,X5] : k3_enumset1(X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X6,X4,X5),k2_tarski(X7,X8)) ),
    inference(superposition,[],[f82,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

fof(f3432,plain,(
    ! [X39,X41,X42,X40] : k3_enumset1(X39,X40,X41,X41,X42) = k2_enumset1(X39,X40,X41,X42) ),
    inference(forward_demodulation,[],[f3380,f30])).

fof(f3380,plain,(
    ! [X39,X41,X42,X40] : k3_enumset1(X39,X40,X41,X41,X42) = k3_enumset1(X39,X39,X40,X41,X42) ),
    inference(superposition,[],[f2805,f31])).

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
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : run_vampire %s %d
% 0.07/0.26  % Computer   : n015.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % WCLimit    : 600
% 0.07/0.26  % DateTime   : Tue Dec  1 15:29:38 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.12/0.33  % (19275)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.12/0.33  % (19274)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.12/0.33  % (19282)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.12/0.34  % (19283)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.12/0.37  % (19270)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.12/0.37  % (19281)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.12/0.37  % (19273)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.12/0.38  % (19272)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.12/0.38  % (19278)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.12/0.38  % (19280)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.12/0.38  % (19284)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.12/0.38  % (19280)Refutation not found, incomplete strategy% (19280)------------------------------
% 0.12/0.38  % (19280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.38  % (19280)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.38  
% 0.12/0.38  % (19280)Memory used [KB]: 10618
% 0.12/0.38  % (19280)Time elapsed: 0.051 s
% 0.12/0.38  % (19280)------------------------------
% 0.12/0.38  % (19280)------------------------------
% 0.12/0.39  % (19276)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.12/0.40  % (19285)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.12/0.40  % (19269)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.12/0.41  % (19279)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.12/0.42  % (19271)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.12/0.43  % (19277)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.12/0.44  % (19286)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 2.53/0.61  % (19285)Refutation found. Thanks to Tanya!
% 2.53/0.61  % SZS status Theorem for theBenchmark
% 2.53/0.61  % SZS output start Proof for theBenchmark
% 2.53/0.61  fof(f5812,plain,(
% 2.53/0.61    $false),
% 2.53/0.61    inference(subsumption_resolution,[],[f22,f5760])).
% 2.53/0.61  fof(f5760,plain,(
% 2.53/0.61    ( ! [X54,X52,X55,X53] : (k2_enumset1(X52,X54,X53,X55) = k2_enumset1(X54,X52,X53,X55)) )),
% 2.53/0.61    inference(superposition,[],[f5147,f3445])).
% 2.53/0.61  fof(f3445,plain,(
% 2.53/0.61    ( ! [X54,X52,X55,X53] : (k2_enumset1(X52,X53,X54,X55) = k3_enumset1(X52,X54,X53,X54,X55)) )),
% 2.53/0.61    inference(forward_demodulation,[],[f3381,f87])).
% 2.53/0.61  fof(f87,plain,(
% 2.53/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X0,X2,X3)) )),
% 2.53/0.61    inference(forward_demodulation,[],[f85,f30])).
% 2.53/0.61  fof(f30,plain,(
% 2.53/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.53/0.61    inference(cnf_transformation,[],[f13])).
% 2.53/0.61  fof(f13,axiom,(
% 2.53/0.61    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.53/0.61  fof(f85,plain,(
% 2.53/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X1,X0,X2,X3)) )),
% 2.53/0.61    inference(superposition,[],[f83,f31])).
% 2.53/0.61  fof(f31,plain,(
% 2.53/0.61    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.53/0.61    inference(cnf_transformation,[],[f14])).
% 2.53/0.61  fof(f14,axiom,(
% 2.53/0.61    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.53/0.61  fof(f83,plain,(
% 2.53/0.61    ( ! [X21,X19,X17,X20,X18] : (k4_enumset1(X17,X18,X19,X17,X20,X21) = k3_enumset1(X17,X18,X19,X20,X21)) )),
% 2.53/0.61    inference(forward_demodulation,[],[f79,f82])).
% 2.53/0.61  fof(f82,plain,(
% 2.53/0.61    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 2.53/0.61    inference(forward_demodulation,[],[f76,f31])).
% 2.53/0.61  fof(f76,plain,(
% 2.53/0.61    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 2.53/0.61    inference(superposition,[],[f75,f28])).
% 2.53/0.61  fof(f28,plain,(
% 2.53/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.53/0.61    inference(cnf_transformation,[],[f12])).
% 2.53/0.61  fof(f12,axiom,(
% 2.53/0.61    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.53/0.61  fof(f75,plain,(
% 2.53/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 2.53/0.61    inference(forward_demodulation,[],[f73,f32])).
% 2.53/0.61  fof(f32,plain,(
% 2.53/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.53/0.61    inference(cnf_transformation,[],[f15])).
% 2.53/0.61  fof(f15,axiom,(
% 2.53/0.61    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.53/0.61  fof(f73,plain,(
% 2.53/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 2.53/0.61    inference(superposition,[],[f34,f30])).
% 2.53/0.61  fof(f34,plain,(
% 2.53/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 2.53/0.61    inference(cnf_transformation,[],[f5])).
% 2.53/0.61  fof(f5,axiom,(
% 2.53/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 2.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).
% 2.53/0.61  fof(f79,plain,(
% 2.53/0.61    ( ! [X21,X19,X17,X20,X18] : (k4_enumset1(X17,X18,X19,X17,X20,X21) = k2_xboole_0(k1_enumset1(X17,X18,X19),k2_tarski(X20,X21))) )),
% 2.53/0.61    inference(superposition,[],[f75,f53])).
% 2.53/0.61  fof(f53,plain,(
% 2.53/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X0)) )),
% 2.53/0.61    inference(superposition,[],[f29,f28])).
% 2.53/0.61  fof(f29,plain,(
% 2.53/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 2.53/0.61    inference(cnf_transformation,[],[f4])).
% 2.53/0.61  fof(f4,axiom,(
% 2.53/0.61    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 2.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).
% 2.53/0.61  fof(f3381,plain,(
% 2.53/0.61    ( ! [X54,X52,X55,X53] : (k3_enumset1(X52,X54,X53,X54,X55) = k3_enumset1(X52,X53,X52,X54,X55)) )),
% 2.53/0.61    inference(superposition,[],[f2805,f84])).
% 2.53/0.61  fof(f84,plain,(
% 2.53/0.61    ( ! [X26,X24,X23,X25,X22] : (k4_enumset1(X22,X23,X22,X24,X25,X26) = k3_enumset1(X22,X24,X23,X25,X26)) )),
% 2.53/0.61    inference(forward_demodulation,[],[f80,f82])).
% 2.53/0.61  fof(f80,plain,(
% 2.53/0.61    ( ! [X26,X24,X23,X25,X22] : (k4_enumset1(X22,X23,X22,X24,X25,X26) = k2_xboole_0(k1_enumset1(X22,X24,X23),k2_tarski(X25,X26))) )),
% 2.53/0.61    inference(superposition,[],[f75,f55])).
% 2.53/0.61  fof(f55,plain,(
% 2.53/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X0,X1)) )),
% 2.53/0.61    inference(superposition,[],[f29,f28])).
% 2.53/0.61  fof(f2805,plain,(
% 2.53/0.61    ( ! [X68,X66,X69,X67,X65] : (k4_enumset1(X65,X66,X67,X68,X68,X69) = k3_enumset1(X65,X66,X67,X68,X69)) )),
% 2.53/0.61    inference(forward_demodulation,[],[f2749,f31])).
% 2.53/0.61  fof(f2749,plain,(
% 2.53/0.61    ( ! [X68,X66,X69,X67,X65] : (k4_enumset1(X65,X66,X67,X68,X68,X69) = k4_enumset1(X65,X65,X66,X67,X68,X69)) )),
% 2.53/0.61    inference(superposition,[],[f2721,f32])).
% 2.53/0.61  fof(f2721,plain,(
% 2.53/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X3,X4,X4,X5)) )),
% 2.53/0.61    inference(forward_demodulation,[],[f2715,f32])).
% 2.53/0.61  fof(f2715,plain,(
% 2.53/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X3,X4,X4,X5)) )),
% 2.53/0.61    inference(superposition,[],[f2651,f33])).
% 2.53/0.61  fof(f33,plain,(
% 2.53/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.53/0.61    inference(cnf_transformation,[],[f16])).
% 2.53/0.61  fof(f16,axiom,(
% 2.53/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 2.53/0.61  fof(f2651,plain,(
% 2.53/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X2,X3,X4,X5,X6,X0,X0,X1) = k5_enumset1(X2,X3,X4,X5,X6,X0,X1)) )),
% 2.53/0.61    inference(forward_demodulation,[],[f2643,f34])).
% 2.53/0.61  fof(f2643,plain,(
% 2.53/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X2,X3,X4,X5,X6,X0,X0,X1) = k2_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k2_tarski(X0,X1))) )),
% 2.53/0.61    inference(superposition,[],[f36,f24])).
% 2.53/0.61  fof(f24,plain,(
% 2.53/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.53/0.61    inference(cnf_transformation,[],[f11])).
% 2.53/0.61  fof(f11,axiom,(
% 2.53/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.53/0.61  fof(f36,plain,(
% 2.53/0.61    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) )),
% 2.53/0.61    inference(cnf_transformation,[],[f7])).
% 2.53/0.61  fof(f7,axiom,(
% 2.53/0.61    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))),
% 2.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).
% 2.53/0.61  fof(f5147,plain,(
% 2.53/0.61    ( ! [X70,X72,X71,X73] : (k2_enumset1(X70,X71,X72,X73) = k3_enumset1(X71,X72,X70,X72,X73)) )),
% 2.53/0.61    inference(superposition,[],[f3432,f494])).
% 2.53/0.61  fof(f494,plain,(
% 2.53/0.61    ( ! [X6,X8,X7,X5,X9] : (k3_enumset1(X5,X6,X7,X8,X9) = k3_enumset1(X6,X7,X5,X8,X9)) )),
% 2.53/0.61    inference(superposition,[],[f100,f82])).
% 2.53/0.61  fof(f100,plain,(
% 2.53/0.61    ( ! [X6,X4,X8,X7,X5] : (k3_enumset1(X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X6,X4,X5),k2_tarski(X7,X8))) )),
% 2.53/0.61    inference(superposition,[],[f82,f27])).
% 2.53/0.61  fof(f27,plain,(
% 2.53/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 2.53/0.61    inference(cnf_transformation,[],[f3])).
% 2.53/0.61  fof(f3,axiom,(
% 2.53/0.61    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 2.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).
% 2.53/0.61  fof(f3432,plain,(
% 2.53/0.61    ( ! [X39,X41,X42,X40] : (k3_enumset1(X39,X40,X41,X41,X42) = k2_enumset1(X39,X40,X41,X42)) )),
% 2.53/0.61    inference(forward_demodulation,[],[f3380,f30])).
% 2.53/0.61  fof(f3380,plain,(
% 2.53/0.61    ( ! [X39,X41,X42,X40] : (k3_enumset1(X39,X40,X41,X41,X42) = k3_enumset1(X39,X39,X40,X41,X42)) )),
% 2.53/0.61    inference(superposition,[],[f2805,f31])).
% 2.53/0.61  fof(f22,plain,(
% 2.53/0.61    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 2.53/0.61    inference(cnf_transformation,[],[f21])).
% 2.53/0.61  fof(f21,plain,(
% 2.53/0.61    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 2.53/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f20])).
% 2.53/0.61  fof(f20,plain,(
% 2.53/0.61    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 2.53/0.61    introduced(choice_axiom,[])).
% 2.53/0.61  fof(f19,plain,(
% 2.53/0.61    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 2.53/0.61    inference(ennf_transformation,[],[f18])).
% 2.53/0.61  fof(f18,negated_conjecture,(
% 2.53/0.61    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 2.53/0.61    inference(negated_conjecture,[],[f17])).
% 2.53/0.61  fof(f17,conjecture,(
% 2.53/0.61    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 2.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).
% 2.53/0.61  % SZS output end Proof for theBenchmark
% 2.53/0.61  % (19285)------------------------------
% 2.53/0.61  % (19285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.53/0.61  % (19285)Termination reason: Refutation
% 2.53/0.61  
% 2.53/0.61  % (19285)Memory used [KB]: 8699
% 2.53/0.61  % (19285)Time elapsed: 0.288 s
% 2.53/0.61  % (19285)------------------------------
% 2.53/0.61  % (19285)------------------------------
% 2.53/0.61  % (19266)Success in time 0.338 s
%------------------------------------------------------------------------------
