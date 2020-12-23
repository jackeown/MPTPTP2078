%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:22 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 318 expanded)
%              Number of leaves         :   10 ( 110 expanded)
%              Depth                    :   14
%              Number of atoms          :   51 ( 319 expanded)
%              Number of equality atoms :   50 ( 318 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f915,plain,(
    $false ),
    inference(subsumption_resolution,[],[f914,f174])).

fof(f174,plain,(
    ! [X6,X8,X7] : k5_xboole_0(X6,X7) = k5_xboole_0(k5_xboole_0(X6,k5_xboole_0(X7,X8)),X8) ),
    inference(superposition,[],[f153,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f153,plain,(
    ! [X2,X3] : k5_xboole_0(k5_xboole_0(X2,X3),X3) = X2 ),
    inference(superposition,[],[f144,f97])).

fof(f97,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(forward_demodulation,[],[f94,f93])).

fof(f93,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(forward_demodulation,[],[f83,f21])).

fof(f21,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f83,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f51,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f33,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f24,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ),
    inference(definition_unfolding,[],[f22,f26,f31])).

fof(f22,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f51,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f28,f38])).

fof(f94,plain,(
    ! [X2,X1] : k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2)) = X2 ),
    inference(backward_demodulation,[],[f75,f93])).

fof(f75,plain,(
    ! [X2,X1] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f28,f59])).

fof(f59,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),X2) ),
    inference(superposition,[],[f50,f38])).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f28,f21])).

fof(f144,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f133,f21])).

fof(f133,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f97,f54])).

fof(f54,plain,(
    ! [X6,X5] : k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6))) ),
    inference(superposition,[],[f28,f38])).

fof(f914,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f913,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f913,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK1,sK0)) ),
    inference(backward_demodulation,[],[f39,f815])).

fof(f815,plain,(
    ! [X43,X41,X42] : k3_xboole_0(X41,k3_xboole_0(X43,k5_xboole_0(X41,k5_xboole_0(X42,k3_xboole_0(X41,X42))))) = k3_xboole_0(X43,X41) ),
    inference(superposition,[],[f411,f246])).

fof(f246,plain,(
    ! [X0,X1] : k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X1 ),
    inference(superposition,[],[f34,f23])).

fof(f411,plain,(
    ! [X4,X5,X3] : k3_xboole_0(X3,k3_xboole_0(X4,X5)) = k3_xboole_0(X4,k3_xboole_0(X3,X5)) ),
    inference(superposition,[],[f229,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f229,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X1,X0),X2) ),
    inference(superposition,[],[f30,f23])).

fof(f39,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) ),
    inference(backward_demodulation,[],[f37,f30])).

fof(f37,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f36,f23])).

fof(f36,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))) ),
    inference(backward_demodulation,[],[f32,f23])).

fof(f32,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f19,f26,f31])).

fof(f19,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:43:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (24637)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (24646)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (24647)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (24647)Refutation not found, incomplete strategy% (24647)------------------------------
% 0.21/0.48  % (24647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (24647)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (24647)Memory used [KB]: 10490
% 0.21/0.48  % (24647)Time elapsed: 0.068 s
% 0.21/0.48  % (24647)------------------------------
% 0.21/0.48  % (24647)------------------------------
% 0.21/0.49  % (24634)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (24645)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.51  % (24648)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % (24653)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (24639)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (24650)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.52  % (24642)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (24641)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.53  % (24643)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.42/0.54  % (24638)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 1.42/0.54  % (24635)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.54/0.56  % (24649)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 1.54/0.56  % (24652)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.54/0.56  % (24651)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.54/0.57  % (24644)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.54/0.59  % (24650)Refutation found. Thanks to Tanya!
% 1.54/0.59  % SZS status Theorem for theBenchmark
% 1.54/0.59  % SZS output start Proof for theBenchmark
% 1.54/0.59  fof(f915,plain,(
% 1.54/0.59    $false),
% 1.54/0.59    inference(subsumption_resolution,[],[f914,f174])).
% 1.54/0.59  fof(f174,plain,(
% 1.54/0.59    ( ! [X6,X8,X7] : (k5_xboole_0(X6,X7) = k5_xboole_0(k5_xboole_0(X6,k5_xboole_0(X7,X8)),X8)) )),
% 1.54/0.59    inference(superposition,[],[f153,f28])).
% 1.54/0.59  fof(f28,plain,(
% 1.54/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.54/0.59    inference(cnf_transformation,[],[f10])).
% 1.54/0.59  fof(f10,axiom,(
% 1.54/0.59    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.54/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.54/0.59  fof(f153,plain,(
% 1.54/0.59    ( ! [X2,X3] : (k5_xboole_0(k5_xboole_0(X2,X3),X3) = X2) )),
% 1.54/0.59    inference(superposition,[],[f144,f97])).
% 1.54/0.59  fof(f97,plain,(
% 1.54/0.59    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2) )),
% 1.54/0.59    inference(forward_demodulation,[],[f94,f93])).
% 1.54/0.59  fof(f93,plain,(
% 1.54/0.59    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.54/0.59    inference(forward_demodulation,[],[f83,f21])).
% 1.54/0.59  fof(f21,plain,(
% 1.54/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.54/0.59    inference(cnf_transformation,[],[f8])).
% 1.54/0.59  fof(f8,axiom,(
% 1.54/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.54/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.54/0.59  fof(f83,plain,(
% 1.54/0.59    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X1,k1_xboole_0)) )),
% 1.54/0.59    inference(superposition,[],[f51,f38])).
% 1.54/0.59  fof(f38,plain,(
% 1.54/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.54/0.59    inference(backward_demodulation,[],[f33,f34])).
% 1.54/0.59  fof(f34,plain,(
% 1.54/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 1.54/0.59    inference(definition_unfolding,[],[f24,f31])).
% 1.54/0.59  fof(f31,plain,(
% 1.54/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.54/0.59    inference(definition_unfolding,[],[f25,f26])).
% 1.54/0.59  fof(f26,plain,(
% 1.54/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.54/0.59    inference(cnf_transformation,[],[f3])).
% 1.54/0.59  fof(f3,axiom,(
% 1.54/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.54/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.54/0.59  fof(f25,plain,(
% 1.54/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.54/0.59    inference(cnf_transformation,[],[f11])).
% 1.54/0.59  fof(f11,axiom,(
% 1.54/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.54/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.54/0.59  fof(f24,plain,(
% 1.54/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.54/0.59    inference(cnf_transformation,[],[f5])).
% 1.54/0.59  fof(f5,axiom,(
% 1.54/0.59    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.54/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 1.54/0.59  fof(f33,plain,(
% 1.54/0.59    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) )),
% 1.54/0.59    inference(definition_unfolding,[],[f22,f26,f31])).
% 1.54/0.59  fof(f22,plain,(
% 1.54/0.59    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.54/0.59    inference(cnf_transformation,[],[f6])).
% 1.54/0.59  fof(f6,axiom,(
% 1.54/0.59    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.54/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.54/0.59  fof(f51,plain,(
% 1.54/0.59    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)) )),
% 1.54/0.59    inference(superposition,[],[f28,f38])).
% 1.54/0.59  fof(f94,plain,(
% 1.54/0.59    ( ! [X2,X1] : (k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2)) = X2) )),
% 1.54/0.59    inference(backward_demodulation,[],[f75,f93])).
% 1.54/0.59  fof(f75,plain,(
% 1.54/0.59    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2))) )),
% 1.54/0.59    inference(superposition,[],[f28,f59])).
% 1.54/0.59  fof(f59,plain,(
% 1.54/0.59    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),X2)) )),
% 1.54/0.59    inference(superposition,[],[f50,f38])).
% 1.54/0.59  fof(f50,plain,(
% 1.54/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) )),
% 1.54/0.59    inference(superposition,[],[f28,f21])).
% 1.54/0.59  fof(f144,plain,(
% 1.54/0.59    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 1.54/0.59    inference(forward_demodulation,[],[f133,f21])).
% 1.54/0.59  fof(f133,plain,(
% 1.54/0.59    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 1.54/0.59    inference(superposition,[],[f97,f54])).
% 1.54/0.59  fof(f54,plain,(
% 1.54/0.59    ( ! [X6,X5] : (k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6)))) )),
% 1.54/0.59    inference(superposition,[],[f28,f38])).
% 1.54/0.59  fof(f914,plain,(
% 1.54/0.59    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))),
% 1.54/0.59    inference(forward_demodulation,[],[f913,f23])).
% 1.54/0.59  fof(f23,plain,(
% 1.54/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f1])).
% 1.54/0.59  fof(f1,axiom,(
% 1.54/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.54/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.54/0.59  fof(f913,plain,(
% 1.54/0.59    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK1,sK0))),
% 1.54/0.59    inference(backward_demodulation,[],[f39,f815])).
% 1.54/0.59  fof(f815,plain,(
% 1.54/0.59    ( ! [X43,X41,X42] : (k3_xboole_0(X41,k3_xboole_0(X43,k5_xboole_0(X41,k5_xboole_0(X42,k3_xboole_0(X41,X42))))) = k3_xboole_0(X43,X41)) )),
% 1.54/0.59    inference(superposition,[],[f411,f246])).
% 1.54/0.59  fof(f246,plain,(
% 1.54/0.59    ( ! [X0,X1] : (k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X1) )),
% 1.54/0.59    inference(superposition,[],[f34,f23])).
% 1.54/0.59  fof(f411,plain,(
% 1.54/0.59    ( ! [X4,X5,X3] : (k3_xboole_0(X3,k3_xboole_0(X4,X5)) = k3_xboole_0(X4,k3_xboole_0(X3,X5))) )),
% 1.54/0.59    inference(superposition,[],[f229,f30])).
% 1.54/0.59  fof(f30,plain,(
% 1.54/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.54/0.59    inference(cnf_transformation,[],[f4])).
% 1.54/0.59  fof(f4,axiom,(
% 1.54/0.59    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.54/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.54/0.59  fof(f229,plain,(
% 1.54/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X1,X0),X2)) )),
% 1.54/0.59    inference(superposition,[],[f30,f23])).
% 1.54/0.59  fof(f39,plain,(
% 1.54/0.59    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))),
% 1.54/0.59    inference(backward_demodulation,[],[f37,f30])).
% 1.54/0.59  fof(f37,plain,(
% 1.54/0.59    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))),
% 1.54/0.59    inference(forward_demodulation,[],[f36,f23])).
% 1.54/0.59  fof(f36,plain,(
% 1.54/0.59    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))),
% 1.54/0.59    inference(backward_demodulation,[],[f32,f23])).
% 1.54/0.59  fof(f32,plain,(
% 1.54/0.59    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1)))),
% 1.54/0.59    inference(definition_unfolding,[],[f19,f26,f31])).
% 1.54/0.59  fof(f19,plain,(
% 1.54/0.59    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.54/0.59    inference(cnf_transformation,[],[f18])).
% 1.54/0.59  fof(f18,plain,(
% 1.54/0.59    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.54/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).
% 1.54/0.59  fof(f17,plain,(
% 1.54/0.59    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.54/0.59    introduced(choice_axiom,[])).
% 1.54/0.59  fof(f15,plain,(
% 1.54/0.59    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.54/0.59    inference(ennf_transformation,[],[f13])).
% 1.54/0.59  fof(f13,negated_conjecture,(
% 1.54/0.59    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.54/0.59    inference(negated_conjecture,[],[f12])).
% 1.54/0.59  fof(f12,conjecture,(
% 1.54/0.59    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.54/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 1.54/0.59  % SZS output end Proof for theBenchmark
% 1.54/0.59  % (24650)------------------------------
% 1.54/0.59  % (24650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.59  % (24650)Termination reason: Refutation
% 1.54/0.59  
% 1.54/0.59  % (24650)Memory used [KB]: 6908
% 1.54/0.59  % (24650)Time elapsed: 0.143 s
% 1.54/0.59  % (24650)------------------------------
% 1.54/0.59  % (24650)------------------------------
% 1.54/0.59  % (24631)Success in time 0.23 s
%------------------------------------------------------------------------------
