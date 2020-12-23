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
% DateTime   : Thu Dec  3 12:32:25 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
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
fof(f909,plain,(
    $false ),
    inference(subsumption_resolution,[],[f908,f169])).

fof(f169,plain,(
    ! [X6,X8,X7] : k5_xboole_0(X6,X7) = k5_xboole_0(k5_xboole_0(X6,k5_xboole_0(X7,X8)),X8) ),
    inference(superposition,[],[f148,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f148,plain,(
    ! [X2,X3] : k5_xboole_0(k5_xboole_0(X2,X3),X3) = X2 ),
    inference(superposition,[],[f139,f92])).

fof(f92,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(forward_demodulation,[],[f89,f88])).

fof(f88,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(forward_demodulation,[],[f78,f18])).

fof(f18,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f78,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f46,f34])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f29,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f21,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ),
    inference(definition_unfolding,[],[f19,f23,f27])).

fof(f19,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f46,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f24,f34])).

fof(f89,plain,(
    ! [X2,X1] : k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2)) = X2 ),
    inference(backward_demodulation,[],[f70,f88])).

fof(f70,plain,(
    ! [X2,X1] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f24,f54])).

fof(f54,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),X2) ),
    inference(superposition,[],[f45,f34])).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f24,f18])).

fof(f139,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f128,f18])).

fof(f128,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f92,f49])).

fof(f49,plain,(
    ! [X6,X5] : k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6))) ),
    inference(superposition,[],[f24,f34])).

fof(f908,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f907,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f907,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK1,sK0)) ),
    inference(backward_demodulation,[],[f35,f809])).

fof(f809,plain,(
    ! [X39,X41,X40] : k3_xboole_0(X39,k3_xboole_0(X41,k5_xboole_0(X39,k5_xboole_0(X40,k3_xboole_0(X39,X40))))) = k3_xboole_0(X41,X39) ),
    inference(superposition,[],[f406,f242])).

fof(f242,plain,(
    ! [X2,X1] : k3_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) = X2 ),
    inference(superposition,[],[f30,f20])).

fof(f406,plain,(
    ! [X4,X5,X3] : k3_xboole_0(X3,k3_xboole_0(X4,X5)) = k3_xboole_0(X4,k3_xboole_0(X3,X5)) ),
    inference(superposition,[],[f225,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f225,plain,(
    ! [X4,X2,X3] : k3_xboole_0(X2,k3_xboole_0(X3,X4)) = k3_xboole_0(k3_xboole_0(X3,X2),X4) ),
    inference(superposition,[],[f26,f20])).

fof(f35,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) ),
    inference(backward_demodulation,[],[f33,f26])).

fof(f33,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f32,f20])).

fof(f32,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))) ),
    inference(backward_demodulation,[],[f28,f20])).

fof(f28,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f16,f23,f27])).

fof(f16,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n003.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 10:42:57 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.19/0.46  % (18413)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.46  % (18417)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.47  % (18411)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.48  % (18419)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.48  % (18423)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.48  % (18414)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.48  % (18421)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.48  % (18422)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.48  % (18424)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.48  % (18415)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.48  % (18416)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.49  % (18425)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.19/0.52  % (18426)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.52  % (18418)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.52  % (18409)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.53  % (18410)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.53  % (18412)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 1.51/0.54  % (18420)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.51/0.54  % (18420)Refutation not found, incomplete strategy% (18420)------------------------------
% 1.51/0.54  % (18420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.54  % (18420)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.54  
% 1.51/0.54  % (18420)Memory used [KB]: 10490
% 1.51/0.54  % (18420)Time elapsed: 0.133 s
% 1.51/0.54  % (18420)------------------------------
% 1.51/0.54  % (18420)------------------------------
% 1.61/0.55  % (18423)Refutation found. Thanks to Tanya!
% 1.61/0.55  % SZS status Theorem for theBenchmark
% 1.61/0.55  % SZS output start Proof for theBenchmark
% 1.61/0.55  fof(f909,plain,(
% 1.61/0.55    $false),
% 1.61/0.55    inference(subsumption_resolution,[],[f908,f169])).
% 1.61/0.55  fof(f169,plain,(
% 1.61/0.55    ( ! [X6,X8,X7] : (k5_xboole_0(X6,X7) = k5_xboole_0(k5_xboole_0(X6,k5_xboole_0(X7,X8)),X8)) )),
% 1.61/0.55    inference(superposition,[],[f148,f24])).
% 1.61/0.55  fof(f24,plain,(
% 1.61/0.55    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.61/0.55    inference(cnf_transformation,[],[f9])).
% 1.61/0.55  fof(f9,axiom,(
% 1.61/0.55    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.61/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.61/0.55  fof(f148,plain,(
% 1.61/0.55    ( ! [X2,X3] : (k5_xboole_0(k5_xboole_0(X2,X3),X3) = X2) )),
% 1.61/0.55    inference(superposition,[],[f139,f92])).
% 1.61/0.55  fof(f92,plain,(
% 1.61/0.55    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2) )),
% 1.61/0.55    inference(forward_demodulation,[],[f89,f88])).
% 1.61/0.55  fof(f88,plain,(
% 1.61/0.55    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.61/0.55    inference(forward_demodulation,[],[f78,f18])).
% 1.61/0.55  fof(f18,plain,(
% 1.61/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.61/0.55    inference(cnf_transformation,[],[f8])).
% 1.61/0.55  fof(f8,axiom,(
% 1.61/0.55    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.61/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.61/0.55  fof(f78,plain,(
% 1.61/0.55    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X1,k1_xboole_0)) )),
% 1.61/0.55    inference(superposition,[],[f46,f34])).
% 1.61/0.55  fof(f34,plain,(
% 1.61/0.55    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.61/0.55    inference(backward_demodulation,[],[f29,f30])).
% 1.61/0.55  fof(f30,plain,(
% 1.61/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 1.61/0.55    inference(definition_unfolding,[],[f21,f27])).
% 1.61/0.55  fof(f27,plain,(
% 1.61/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.61/0.55    inference(definition_unfolding,[],[f22,f23])).
% 1.61/0.55  fof(f23,plain,(
% 1.61/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.61/0.55    inference(cnf_transformation,[],[f2])).
% 1.61/0.55  fof(f2,axiom,(
% 1.61/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.61/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.61/0.55  fof(f22,plain,(
% 1.61/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.61/0.55    inference(cnf_transformation,[],[f10])).
% 1.61/0.55  fof(f10,axiom,(
% 1.61/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.61/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.61/0.55  fof(f21,plain,(
% 1.61/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.61/0.55    inference(cnf_transformation,[],[f4])).
% 1.61/0.55  fof(f4,axiom,(
% 1.61/0.55    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.61/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 1.61/0.55  fof(f29,plain,(
% 1.61/0.55    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) )),
% 1.61/0.55    inference(definition_unfolding,[],[f19,f23,f27])).
% 1.61/0.55  fof(f19,plain,(
% 1.61/0.55    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.61/0.55    inference(cnf_transformation,[],[f6])).
% 1.61/0.55  fof(f6,axiom,(
% 1.61/0.55    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.61/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.61/0.55  fof(f46,plain,(
% 1.61/0.55    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)) )),
% 1.61/0.55    inference(superposition,[],[f24,f34])).
% 1.61/0.55  fof(f89,plain,(
% 1.61/0.55    ( ! [X2,X1] : (k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2)) = X2) )),
% 1.61/0.55    inference(backward_demodulation,[],[f70,f88])).
% 1.61/0.55  fof(f70,plain,(
% 1.61/0.55    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2))) )),
% 1.61/0.55    inference(superposition,[],[f24,f54])).
% 1.61/0.55  fof(f54,plain,(
% 1.61/0.55    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),X2)) )),
% 1.61/0.55    inference(superposition,[],[f45,f34])).
% 1.61/0.55  fof(f45,plain,(
% 1.61/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) )),
% 1.61/0.55    inference(superposition,[],[f24,f18])).
% 1.61/0.55  fof(f139,plain,(
% 1.61/0.55    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 1.61/0.55    inference(forward_demodulation,[],[f128,f18])).
% 1.61/0.55  fof(f128,plain,(
% 1.61/0.55    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 1.61/0.55    inference(superposition,[],[f92,f49])).
% 1.61/0.55  fof(f49,plain,(
% 1.61/0.55    ( ! [X6,X5] : (k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6)))) )),
% 1.61/0.55    inference(superposition,[],[f24,f34])).
% 1.61/0.55  fof(f908,plain,(
% 1.61/0.55    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))),
% 1.61/0.55    inference(forward_demodulation,[],[f907,f20])).
% 1.61/0.55  fof(f20,plain,(
% 1.61/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.61/0.55    inference(cnf_transformation,[],[f1])).
% 1.61/0.55  fof(f1,axiom,(
% 1.61/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.61/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.61/0.55  fof(f907,plain,(
% 1.61/0.55    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK1,sK0))),
% 1.61/0.55    inference(backward_demodulation,[],[f35,f809])).
% 1.61/0.55  fof(f809,plain,(
% 1.61/0.55    ( ! [X39,X41,X40] : (k3_xboole_0(X39,k3_xboole_0(X41,k5_xboole_0(X39,k5_xboole_0(X40,k3_xboole_0(X39,X40))))) = k3_xboole_0(X41,X39)) )),
% 1.61/0.55    inference(superposition,[],[f406,f242])).
% 1.61/0.55  fof(f242,plain,(
% 1.61/0.55    ( ! [X2,X1] : (k3_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) = X2) )),
% 1.61/0.55    inference(superposition,[],[f30,f20])).
% 1.61/0.55  fof(f406,plain,(
% 1.61/0.55    ( ! [X4,X5,X3] : (k3_xboole_0(X3,k3_xboole_0(X4,X5)) = k3_xboole_0(X4,k3_xboole_0(X3,X5))) )),
% 1.61/0.55    inference(superposition,[],[f225,f26])).
% 1.61/0.55  fof(f26,plain,(
% 1.61/0.55    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.61/0.55    inference(cnf_transformation,[],[f3])).
% 1.61/0.55  fof(f3,axiom,(
% 1.61/0.55    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.61/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.61/0.55  fof(f225,plain,(
% 1.61/0.55    ( ! [X4,X2,X3] : (k3_xboole_0(X2,k3_xboole_0(X3,X4)) = k3_xboole_0(k3_xboole_0(X3,X2),X4)) )),
% 1.61/0.55    inference(superposition,[],[f26,f20])).
% 1.61/0.55  fof(f35,plain,(
% 1.61/0.55    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))),
% 1.61/0.55    inference(backward_demodulation,[],[f33,f26])).
% 1.61/0.55  fof(f33,plain,(
% 1.61/0.55    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))),
% 1.61/0.55    inference(forward_demodulation,[],[f32,f20])).
% 1.61/0.55  fof(f32,plain,(
% 1.61/0.55    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))),
% 1.61/0.55    inference(backward_demodulation,[],[f28,f20])).
% 1.61/0.55  fof(f28,plain,(
% 1.61/0.55    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1)))),
% 1.61/0.55    inference(definition_unfolding,[],[f16,f23,f27])).
% 1.61/0.55  fof(f16,plain,(
% 1.61/0.55    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.61/0.55    inference(cnf_transformation,[],[f15])).
% 1.61/0.55  fof(f15,plain,(
% 1.61/0.55    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.61/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 1.61/0.55  fof(f14,plain,(
% 1.61/0.55    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.61/0.55    introduced(choice_axiom,[])).
% 1.61/0.55  fof(f13,plain,(
% 1.61/0.55    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.61/0.55    inference(ennf_transformation,[],[f12])).
% 1.61/0.55  fof(f12,negated_conjecture,(
% 1.61/0.55    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.61/0.55    inference(negated_conjecture,[],[f11])).
% 1.61/0.55  fof(f11,conjecture,(
% 1.61/0.55    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.61/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 1.61/0.55  % SZS output end Proof for theBenchmark
% 1.61/0.55  % (18423)------------------------------
% 1.61/0.55  % (18423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.55  % (18423)Termination reason: Refutation
% 1.61/0.55  
% 1.61/0.55  % (18423)Memory used [KB]: 6908
% 1.61/0.55  % (18423)Time elapsed: 0.120 s
% 1.61/0.55  % (18423)------------------------------
% 1.61/0.55  % (18423)------------------------------
% 1.61/0.55  % (18408)Success in time 0.213 s
%------------------------------------------------------------------------------
