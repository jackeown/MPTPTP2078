%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:26 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 308 expanded)
%              Number of leaves         :   11 ( 103 expanded)
%              Depth                    :   17
%              Number of atoms          :   58 ( 309 expanded)
%              Number of equality atoms :   57 ( 308 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1420,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1419])).

fof(f1419,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f1418,f30])).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f27,f16])).

fof(f16,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f27,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f18,f22])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f1418,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1417,f16])).

fof(f1417,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f1416,f17])).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f1416,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)))) ),
    inference(backward_demodulation,[],[f348,f1380])).

fof(f1380,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) = X1 ),
    inference(superposition,[],[f1314,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1314,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,k3_xboole_0(X5,X6)))) = X5 ),
    inference(forward_demodulation,[],[f1313,f142])).

fof(f142,plain,(
    ! [X2,X1] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(superposition,[],[f58,f127])).

fof(f127,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f116,f30])).

fof(f116,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f58,f44])).

fof(f44,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f24,f17])).

fof(f24,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f41,f57])).

fof(f57,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f50,f30])).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f41,f17])).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f24,f17])).

fof(f1313,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(k3_xboole_0(X5,X6),X5))) = X5 ),
    inference(forward_demodulation,[],[f1312,f210])).

fof(f210,plain,(
    ! [X14,X15,X13] : k5_xboole_0(X13,k5_xboole_0(X14,X15)) = k5_xboole_0(X15,k5_xboole_0(X13,X14)) ),
    inference(superposition,[],[f142,f24])).

fof(f1312,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k5_xboole_0(k3_xboole_0(X5,X6),k5_xboole_0(X5,X6))) = X5 ),
    inference(forward_demodulation,[],[f1271,f142])).

fof(f1271,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k5_xboole_0(k5_xboole_0(X5,X6),k3_xboole_0(X5,X6))) = X5 ),
    inference(superposition,[],[f1173,f58])).

fof(f1173,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,k5_xboole_0(X0,X1)))) = X0 ),
    inference(forward_demodulation,[],[f1071,f19])).

fof(f1071,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),X0))) = X0 ),
    inference(superposition,[],[f74,f58])).

fof(f74,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),X2))))) = X2 ),
    inference(superposition,[],[f28,f24])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f20,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f348,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))) ),
    inference(forward_demodulation,[],[f347,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f23,f22,f22])).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f347,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))) ),
    inference(forward_demodulation,[],[f346,f24])).

fof(f346,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) ),
    inference(superposition,[],[f32,f24])).

fof(f32,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f31,f19])).

fof(f31,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))) ),
    inference(backward_demodulation,[],[f26,f19])).

fof(f26,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f15,f22,f25])).

fof(f15,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:19:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (3638)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (3640)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (3635)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (3637)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (3639)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.50  % (3648)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.51  % (3647)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.51  % (3643)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.51  % (3636)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.51  % (3645)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.51  % (3645)Refutation not found, incomplete strategy% (3645)------------------------------
% 0.22/0.51  % (3645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3645)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (3645)Memory used [KB]: 10490
% 0.22/0.51  % (3645)Time elapsed: 0.078 s
% 0.22/0.51  % (3645)------------------------------
% 0.22/0.51  % (3645)------------------------------
% 0.22/0.52  % (3646)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.52  % (3650)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.52  % (3644)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.55  % (3634)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 1.39/0.55  % (3641)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.39/0.56  % (3649)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.39/0.57  % (3651)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.67/0.57  % (3642)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.67/0.62  % (3635)Refutation found. Thanks to Tanya!
% 1.67/0.62  % SZS status Theorem for theBenchmark
% 1.67/0.62  % SZS output start Proof for theBenchmark
% 1.67/0.62  fof(f1420,plain,(
% 1.67/0.62    $false),
% 1.67/0.62    inference(trivial_inequality_removal,[],[f1419])).
% 1.67/0.62  fof(f1419,plain,(
% 1.67/0.62    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1)),
% 1.67/0.62    inference(forward_demodulation,[],[f1418,f30])).
% 1.67/0.62  fof(f30,plain,(
% 1.67/0.62    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.67/0.62    inference(forward_demodulation,[],[f27,f16])).
% 1.67/0.62  fof(f16,plain,(
% 1.67/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.67/0.62    inference(cnf_transformation,[],[f4])).
% 1.67/0.62  fof(f4,axiom,(
% 1.67/0.62    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.67/0.62  fof(f27,plain,(
% 1.67/0.62    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.67/0.62    inference(definition_unfolding,[],[f18,f22])).
% 1.67/0.62  fof(f22,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.67/0.62    inference(cnf_transformation,[],[f2])).
% 1.67/0.62  fof(f2,axiom,(
% 1.67/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.67/0.62  fof(f18,plain,(
% 1.67/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.67/0.62    inference(cnf_transformation,[],[f5])).
% 1.67/0.62  fof(f5,axiom,(
% 1.67/0.62    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.67/0.62  fof(f1418,plain,(
% 1.67/0.62    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0))),
% 1.67/0.62    inference(forward_demodulation,[],[f1417,f16])).
% 1.67/0.62  fof(f1417,plain,(
% 1.67/0.62    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k1_xboole_0)))),
% 1.67/0.62    inference(forward_demodulation,[],[f1416,f17])).
% 1.67/0.62  fof(f17,plain,(
% 1.67/0.62    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.67/0.62    inference(cnf_transformation,[],[f8])).
% 1.67/0.62  fof(f8,axiom,(
% 1.67/0.62    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.67/0.62  fof(f1416,plain,(
% 1.67/0.62    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,sK1))))),
% 1.67/0.62    inference(backward_demodulation,[],[f348,f1380])).
% 1.67/0.62  fof(f1380,plain,(
% 1.67/0.62    ( ! [X2,X1] : (k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) = X1) )),
% 1.67/0.62    inference(superposition,[],[f1314,f19])).
% 1.67/0.62  fof(f19,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.67/0.62    inference(cnf_transformation,[],[f1])).
% 1.67/0.62  fof(f1,axiom,(
% 1.67/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.67/0.62  fof(f1314,plain,(
% 1.67/0.62    ( ! [X6,X5] : (k3_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,k3_xboole_0(X5,X6)))) = X5) )),
% 1.67/0.62    inference(forward_demodulation,[],[f1313,f142])).
% 1.67/0.62  fof(f142,plain,(
% 1.67/0.62    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)) )),
% 1.67/0.62    inference(superposition,[],[f58,f127])).
% 1.67/0.62  fof(f127,plain,(
% 1.67/0.62    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 1.67/0.62    inference(forward_demodulation,[],[f116,f30])).
% 1.67/0.62  fof(f116,plain,(
% 1.67/0.62    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 1.67/0.62    inference(superposition,[],[f58,f44])).
% 1.67/0.62  fof(f44,plain,(
% 1.67/0.62    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 1.67/0.62    inference(superposition,[],[f24,f17])).
% 1.67/0.62  fof(f24,plain,(
% 1.67/0.62    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.67/0.62    inference(cnf_transformation,[],[f7])).
% 1.67/0.62  fof(f7,axiom,(
% 1.67/0.62    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.67/0.62  fof(f58,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.67/0.62    inference(backward_demodulation,[],[f41,f57])).
% 1.67/0.62  fof(f57,plain,(
% 1.67/0.62    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.67/0.62    inference(forward_demodulation,[],[f50,f30])).
% 1.67/0.62  fof(f50,plain,(
% 1.67/0.62    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.67/0.62    inference(superposition,[],[f41,f17])).
% 1.67/0.62  fof(f41,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 1.67/0.62    inference(superposition,[],[f24,f17])).
% 1.67/0.62  fof(f1313,plain,(
% 1.67/0.62    ( ! [X6,X5] : (k3_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(k3_xboole_0(X5,X6),X5))) = X5) )),
% 1.67/0.62    inference(forward_demodulation,[],[f1312,f210])).
% 1.67/0.62  fof(f210,plain,(
% 1.67/0.62    ( ! [X14,X15,X13] : (k5_xboole_0(X13,k5_xboole_0(X14,X15)) = k5_xboole_0(X15,k5_xboole_0(X13,X14))) )),
% 1.67/0.62    inference(superposition,[],[f142,f24])).
% 1.67/0.62  fof(f1312,plain,(
% 1.67/0.62    ( ! [X6,X5] : (k3_xboole_0(X5,k5_xboole_0(k3_xboole_0(X5,X6),k5_xboole_0(X5,X6))) = X5) )),
% 1.67/0.62    inference(forward_demodulation,[],[f1271,f142])).
% 1.67/0.62  fof(f1271,plain,(
% 1.67/0.62    ( ! [X6,X5] : (k3_xboole_0(X5,k5_xboole_0(k5_xboole_0(X5,X6),k3_xboole_0(X5,X6))) = X5) )),
% 1.67/0.62    inference(superposition,[],[f1173,f58])).
% 1.67/0.62  fof(f1173,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,k5_xboole_0(X0,X1)))) = X0) )),
% 1.67/0.62    inference(forward_demodulation,[],[f1071,f19])).
% 1.67/0.62  fof(f1071,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),X0))) = X0) )),
% 1.67/0.62    inference(superposition,[],[f74,f58])).
% 1.67/0.62  fof(f74,plain,(
% 1.67/0.62    ( ! [X2,X0,X1] : (k3_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),X2))))) = X2) )),
% 1.67/0.62    inference(superposition,[],[f28,f24])).
% 1.67/0.62  fof(f28,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 1.67/0.62    inference(definition_unfolding,[],[f20,f25])).
% 1.67/0.62  fof(f25,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.67/0.62    inference(definition_unfolding,[],[f21,f22])).
% 1.67/0.62  fof(f21,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.67/0.62    inference(cnf_transformation,[],[f9])).
% 1.67/0.62  fof(f9,axiom,(
% 1.67/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.67/0.62  fof(f20,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.67/0.62    inference(cnf_transformation,[],[f3])).
% 1.67/0.62  fof(f3,axiom,(
% 1.67/0.62    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 1.67/0.62  fof(f348,plain,(
% 1.67/0.62    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))))),
% 1.67/0.62    inference(forward_demodulation,[],[f347,f29])).
% 1.67/0.62  fof(f29,plain,(
% 1.67/0.62    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 1.67/0.62    inference(definition_unfolding,[],[f23,f22,f22])).
% 1.67/0.62  fof(f23,plain,(
% 1.67/0.62    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.67/0.62    inference(cnf_transformation,[],[f6])).
% 1.67/0.62  fof(f6,axiom,(
% 1.67/0.62    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.67/0.62  fof(f347,plain,(
% 1.67/0.62    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))),
% 1.67/0.62    inference(forward_demodulation,[],[f346,f24])).
% 1.67/0.62  fof(f346,plain,(
% 1.67/0.62    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))),
% 1.67/0.62    inference(superposition,[],[f32,f24])).
% 1.67/0.62  fof(f32,plain,(
% 1.67/0.62    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))),
% 1.67/0.62    inference(forward_demodulation,[],[f31,f19])).
% 1.67/0.62  fof(f31,plain,(
% 1.67/0.62    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))),
% 1.67/0.62    inference(backward_demodulation,[],[f26,f19])).
% 1.67/0.62  fof(f26,plain,(
% 1.67/0.62    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1)))),
% 1.67/0.62    inference(definition_unfolding,[],[f15,f22,f25])).
% 1.67/0.62  fof(f15,plain,(
% 1.67/0.62    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.67/0.62    inference(cnf_transformation,[],[f14])).
% 1.67/0.62  fof(f14,plain,(
% 1.67/0.62    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.67/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 1.67/0.62  fof(f13,plain,(
% 1.67/0.62    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.67/0.62    introduced(choice_axiom,[])).
% 1.67/0.62  fof(f12,plain,(
% 1.67/0.62    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.67/0.62    inference(ennf_transformation,[],[f11])).
% 1.67/0.62  fof(f11,negated_conjecture,(
% 1.67/0.62    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.67/0.62    inference(negated_conjecture,[],[f10])).
% 1.67/0.62  fof(f10,conjecture,(
% 1.67/0.62    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
% 1.67/0.62  % SZS output end Proof for theBenchmark
% 1.67/0.62  % (3635)------------------------------
% 1.67/0.62  % (3635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.62  % (3635)Termination reason: Refutation
% 1.67/0.62  
% 1.67/0.62  % (3635)Memory used [KB]: 3709
% 1.67/0.62  % (3635)Time elapsed: 0.190 s
% 1.67/0.62  % (3635)------------------------------
% 1.67/0.62  % (3635)------------------------------
% 1.67/0.62  % (3633)Success in time 0.257 s
%------------------------------------------------------------------------------
