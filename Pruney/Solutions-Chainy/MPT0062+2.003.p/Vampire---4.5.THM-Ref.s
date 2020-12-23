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
% DateTime   : Thu Dec  3 12:30:15 EST 2020

% Result     : Theorem 2.16s
% Output     : Refutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 180 expanded)
%              Number of leaves         :   12 (  61 expanded)
%              Depth                    :   22
%              Number of atoms          :   68 ( 185 expanded)
%              Number of equality atoms :   61 ( 177 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3423,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f3347])).

fof(f3347,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f3346])).

fof(f3346,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f31,f3345])).

fof(f3345,plain,(
    ! [X24,X23,X25] : k4_xboole_0(k2_xboole_0(X23,X25),k4_xboole_0(X23,k4_xboole_0(X23,X24))) = k2_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X25,X23)) ),
    inference(backward_demodulation,[],[f3066,f3265])).

fof(f3265,plain,(
    ! [X52,X50,X51] : k2_xboole_0(k4_xboole_0(X50,X51),k4_xboole_0(X52,k4_xboole_0(X50,k4_xboole_0(X50,X51)))) = k2_xboole_0(k4_xboole_0(X50,X51),k4_xboole_0(X52,X50)) ),
    inference(superposition,[],[f229,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f22,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f229,plain,(
    ! [X10,X8,X9] : k2_xboole_0(X10,k4_xboole_0(X8,X9)) = k2_xboole_0(X10,k4_xboole_0(X8,k2_xboole_0(X9,X10))) ),
    inference(superposition,[],[f20,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f3066,plain,(
    ! [X24,X23,X25] : k4_xboole_0(k2_xboole_0(X23,X25),k4_xboole_0(X23,k4_xboole_0(X23,X24))) = k2_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X25,k4_xboole_0(X23,k4_xboole_0(X23,X24)))) ),
    inference(superposition,[],[f24,f477])).

fof(f477,plain,(
    ! [X8,X7] : k4_xboole_0(X7,X8) = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X7,X8))) ),
    inference(forward_demodulation,[],[f404,f441])).

fof(f441,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X9,X8)) = X8 ),
    inference(forward_demodulation,[],[f440,f16])).

fof(f16,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f440,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X9,X8)) = k4_xboole_0(X8,k1_xboole_0) ),
    inference(backward_demodulation,[],[f275,f439])).

fof(f439,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6)) ),
    inference(backward_demodulation,[],[f117,f412])).

fof(f412,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f49,f411])).

fof(f411,plain,(
    ! [X11] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X11) ),
    inference(backward_demodulation,[],[f291,f381])).

fof(f381,plain,(
    ! [X8] : k1_xboole_0 = k2_xboole_0(k4_xboole_0(X8,X8),k4_xboole_0(k1_xboole_0,X8)) ),
    inference(superposition,[],[f27,f245])).

fof(f245,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f26,f16])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f17,f19,f19])).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f291,plain,(
    ! [X11] : k4_xboole_0(k1_xboole_0,X11) = k2_xboole_0(k4_xboole_0(X11,X11),k4_xboole_0(k1_xboole_0,X11)) ),
    inference(forward_demodulation,[],[f266,f16])).

fof(f266,plain,(
    ! [X11] : k4_xboole_0(k1_xboole_0,X11) = k2_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,k1_xboole_0)),k4_xboole_0(k1_xboole_0,X11)) ),
    inference(superposition,[],[f127,f26])).

fof(f127,plain,(
    ! [X14] : k2_xboole_0(k4_xboole_0(k1_xboole_0,X14),X14) = X14 ),
    inference(superposition,[],[f107,f59])).

fof(f59,plain,(
    ! [X0] : k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f57,f49])).

fof(f57,plain,(
    ! [X0] : k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f55,f39])).

fof(f39,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f36,f16])).

fof(f36,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f21,f16])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f55,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f20,f49])).

fof(f107,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f83,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f83,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f79,f20])).

fof(f79,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f20,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f21,f18])).

fof(f49,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f21,f42])).

fof(f42,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f39,f18])).

fof(f117,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f21,f83])).

fof(f275,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X8,k2_xboole_0(X8,X9))) = k4_xboole_0(X8,k4_xboole_0(X9,X8)) ),
    inference(forward_demodulation,[],[f247,f35])).

fof(f35,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4)) ),
    inference(superposition,[],[f21,f20])).

fof(f247,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X8,k2_xboole_0(X8,X9))) = k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X9,X8)) ),
    inference(superposition,[],[f26,f33])).

fof(f404,plain,(
    ! [X8,X7] : k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X7,k4_xboole_0(X7,X8))) = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X7,X8))) ),
    inference(superposition,[],[f33,f27])).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f31,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl2_1
  <=> k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f32,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f25,f29])).

fof(f25,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f15,f19])).

fof(f15,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))
   => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:06:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (22962)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (22961)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (22963)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (22973)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (22966)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (22974)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (22964)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (22972)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (22965)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (22971)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (22968)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (22976)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.49  % (22970)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (22970)Refutation not found, incomplete strategy% (22970)------------------------------
% 0.22/0.49  % (22970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (22970)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (22970)Memory used [KB]: 10490
% 0.22/0.49  % (22970)Time elapsed: 0.074 s
% 0.22/0.49  % (22970)------------------------------
% 0.22/0.49  % (22970)------------------------------
% 0.22/0.49  % (22960)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (22969)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.50  % (22975)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.50  % (22959)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.51  % (22967)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 2.16/0.66  % (22969)Refutation found. Thanks to Tanya!
% 2.16/0.66  % SZS status Theorem for theBenchmark
% 2.16/0.67  % SZS output start Proof for theBenchmark
% 2.16/0.67  fof(f3423,plain,(
% 2.16/0.67    $false),
% 2.16/0.67    inference(avatar_sat_refutation,[],[f32,f3347])).
% 2.16/0.67  fof(f3347,plain,(
% 2.16/0.67    spl2_1),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f3346])).
% 2.16/0.67  fof(f3346,plain,(
% 2.16/0.67    $false | spl2_1),
% 2.16/0.67    inference(subsumption_resolution,[],[f31,f3345])).
% 2.16/0.67  fof(f3345,plain,(
% 2.16/0.67    ( ! [X24,X23,X25] : (k4_xboole_0(k2_xboole_0(X23,X25),k4_xboole_0(X23,k4_xboole_0(X23,X24))) = k2_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X25,X23))) )),
% 2.16/0.67    inference(backward_demodulation,[],[f3066,f3265])).
% 2.16/0.67  fof(f3265,plain,(
% 2.16/0.67    ( ! [X52,X50,X51] : (k2_xboole_0(k4_xboole_0(X50,X51),k4_xboole_0(X52,k4_xboole_0(X50,k4_xboole_0(X50,X51)))) = k2_xboole_0(k4_xboole_0(X50,X51),k4_xboole_0(X52,X50))) )),
% 2.16/0.67    inference(superposition,[],[f229,f27])).
% 2.16/0.67  fof(f27,plain,(
% 2.16/0.67    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 2.16/0.67    inference(definition_unfolding,[],[f22,f19])).
% 2.16/0.67  fof(f19,plain,(
% 2.16/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f8])).
% 2.16/0.67  fof(f8,axiom,(
% 2.16/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.16/0.67  fof(f22,plain,(
% 2.16/0.67    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.16/0.67    inference(cnf_transformation,[],[f9])).
% 2.16/0.67  fof(f9,axiom,(
% 2.16/0.67    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 2.16/0.67  fof(f229,plain,(
% 2.16/0.67    ( ! [X10,X8,X9] : (k2_xboole_0(X10,k4_xboole_0(X8,X9)) = k2_xboole_0(X10,k4_xboole_0(X8,k2_xboole_0(X9,X10)))) )),
% 2.16/0.67    inference(superposition,[],[f20,f23])).
% 2.16/0.67  fof(f23,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f6])).
% 2.16/0.67  fof(f6,axiom,(
% 2.16/0.67    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.16/0.67  fof(f20,plain,(
% 2.16/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f3])).
% 2.16/0.67  fof(f3,axiom,(
% 2.16/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.16/0.67  fof(f3066,plain,(
% 2.16/0.67    ( ! [X24,X23,X25] : (k4_xboole_0(k2_xboole_0(X23,X25),k4_xboole_0(X23,k4_xboole_0(X23,X24))) = k2_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X25,k4_xboole_0(X23,k4_xboole_0(X23,X24))))) )),
% 2.16/0.67    inference(superposition,[],[f24,f477])).
% 2.16/0.67  fof(f477,plain,(
% 2.16/0.67    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X7,X8)))) )),
% 2.16/0.67    inference(forward_demodulation,[],[f404,f441])).
% 2.16/0.67  fof(f441,plain,(
% 2.16/0.67    ( ! [X8,X9] : (k4_xboole_0(X8,k4_xboole_0(X9,X8)) = X8) )),
% 2.16/0.67    inference(forward_demodulation,[],[f440,f16])).
% 2.16/0.67  fof(f16,plain,(
% 2.16/0.67    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.16/0.67    inference(cnf_transformation,[],[f4])).
% 2.16/0.67  fof(f4,axiom,(
% 2.16/0.67    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.16/0.67  fof(f440,plain,(
% 2.16/0.67    ( ! [X8,X9] : (k4_xboole_0(X8,k4_xboole_0(X9,X8)) = k4_xboole_0(X8,k1_xboole_0)) )),
% 2.16/0.67    inference(backward_demodulation,[],[f275,f439])).
% 2.16/0.67  fof(f439,plain,(
% 2.16/0.67    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6))) )),
% 2.16/0.67    inference(backward_demodulation,[],[f117,f412])).
% 2.16/0.67  fof(f412,plain,(
% 2.16/0.67    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.16/0.67    inference(backward_demodulation,[],[f49,f411])).
% 2.16/0.67  fof(f411,plain,(
% 2.16/0.67    ( ! [X11] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X11)) )),
% 2.16/0.67    inference(backward_demodulation,[],[f291,f381])).
% 2.16/0.67  fof(f381,plain,(
% 2.16/0.67    ( ! [X8] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(X8,X8),k4_xboole_0(k1_xboole_0,X8))) )),
% 2.16/0.67    inference(superposition,[],[f27,f245])).
% 2.16/0.67  fof(f245,plain,(
% 2.16/0.67    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 2.16/0.67    inference(superposition,[],[f26,f16])).
% 2.16/0.67  fof(f26,plain,(
% 2.16/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.16/0.67    inference(definition_unfolding,[],[f17,f19,f19])).
% 2.16/0.67  fof(f17,plain,(
% 2.16/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f2])).
% 2.16/0.67  fof(f2,axiom,(
% 2.16/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.16/0.67  fof(f291,plain,(
% 2.16/0.67    ( ! [X11] : (k4_xboole_0(k1_xboole_0,X11) = k2_xboole_0(k4_xboole_0(X11,X11),k4_xboole_0(k1_xboole_0,X11))) )),
% 2.16/0.67    inference(forward_demodulation,[],[f266,f16])).
% 2.16/0.67  fof(f266,plain,(
% 2.16/0.67    ( ! [X11] : (k4_xboole_0(k1_xboole_0,X11) = k2_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,k1_xboole_0)),k4_xboole_0(k1_xboole_0,X11))) )),
% 2.16/0.67    inference(superposition,[],[f127,f26])).
% 2.16/0.67  fof(f127,plain,(
% 2.16/0.67    ( ! [X14] : (k2_xboole_0(k4_xboole_0(k1_xboole_0,X14),X14) = X14) )),
% 2.16/0.67    inference(superposition,[],[f107,f59])).
% 2.16/0.67  fof(f59,plain,(
% 2.16/0.67    ( ! [X0] : (k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 2.16/0.67    inference(superposition,[],[f57,f49])).
% 2.16/0.67  fof(f57,plain,(
% 2.16/0.67    ( ! [X0] : (k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 2.16/0.67    inference(forward_demodulation,[],[f55,f39])).
% 2.16/0.67  fof(f39,plain,(
% 2.16/0.67    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 2.16/0.67    inference(forward_demodulation,[],[f36,f16])).
% 2.16/0.67  fof(f36,plain,(
% 2.16/0.67    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 2.16/0.67    inference(superposition,[],[f21,f16])).
% 2.16/0.67  fof(f21,plain,(
% 2.16/0.67    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f5])).
% 2.16/0.67  fof(f5,axiom,(
% 2.16/0.67    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.16/0.67  fof(f55,plain,(
% 2.16/0.67    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X0,X0))) )),
% 2.16/0.67    inference(superposition,[],[f20,f49])).
% 2.16/0.67  fof(f107,plain,(
% 2.16/0.67    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 2.16/0.67    inference(superposition,[],[f83,f18])).
% 2.16/0.67  fof(f18,plain,(
% 2.16/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f1])).
% 2.16/0.67  fof(f1,axiom,(
% 2.16/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.16/0.67  fof(f83,plain,(
% 2.16/0.67    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 2.16/0.67    inference(forward_demodulation,[],[f79,f20])).
% 2.16/0.67  fof(f79,plain,(
% 2.16/0.67    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 2.16/0.67    inference(superposition,[],[f20,f33])).
% 2.16/0.67  fof(f33,plain,(
% 2.16/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 2.16/0.67    inference(superposition,[],[f21,f18])).
% 2.16/0.67  fof(f49,plain,(
% 2.16/0.67    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0)) )),
% 2.16/0.67    inference(superposition,[],[f21,f42])).
% 2.16/0.67  fof(f42,plain,(
% 2.16/0.67    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.16/0.67    inference(superposition,[],[f39,f18])).
% 2.16/0.67  fof(f117,plain,(
% 2.16/0.67    ( ! [X6,X5] : (k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6))) )),
% 2.16/0.67    inference(superposition,[],[f21,f83])).
% 2.16/0.67  fof(f275,plain,(
% 2.16/0.67    ( ! [X8,X9] : (k4_xboole_0(X8,k4_xboole_0(X8,k2_xboole_0(X8,X9))) = k4_xboole_0(X8,k4_xboole_0(X9,X8))) )),
% 2.16/0.67    inference(forward_demodulation,[],[f247,f35])).
% 2.16/0.67  fof(f35,plain,(
% 2.16/0.67    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4))) )),
% 2.16/0.67    inference(superposition,[],[f21,f20])).
% 2.16/0.67  fof(f247,plain,(
% 2.16/0.67    ( ! [X8,X9] : (k4_xboole_0(X8,k4_xboole_0(X8,k2_xboole_0(X8,X9))) = k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X9,X8))) )),
% 2.16/0.67    inference(superposition,[],[f26,f33])).
% 2.16/0.67  fof(f404,plain,(
% 2.16/0.67    ( ! [X8,X7] : (k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X7,k4_xboole_0(X7,X8))) = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X7,X8)))) )),
% 2.16/0.67    inference(superposition,[],[f33,f27])).
% 2.16/0.67  fof(f24,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f7])).
% 2.16/0.67  fof(f7,axiom,(
% 2.16/0.67    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
% 2.16/0.67  fof(f31,plain,(
% 2.16/0.67    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_1),
% 2.16/0.67    inference(avatar_component_clause,[],[f29])).
% 2.16/0.67  fof(f29,plain,(
% 2.16/0.67    spl2_1 <=> k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.16/0.67  fof(f32,plain,(
% 2.16/0.67    ~spl2_1),
% 2.16/0.67    inference(avatar_split_clause,[],[f25,f29])).
% 2.16/0.67  fof(f25,plain,(
% 2.16/0.67    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.16/0.67    inference(definition_unfolding,[],[f15,f19])).
% 2.16/0.67  fof(f15,plain,(
% 2.16/0.67    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 2.16/0.67    inference(cnf_transformation,[],[f14])).
% 2.16/0.67  fof(f14,plain,(
% 2.16/0.67    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 2.16/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 2.16/0.67  fof(f13,plain,(
% 2.16/0.67    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 2.16/0.67    introduced(choice_axiom,[])).
% 2.16/0.67  fof(f12,plain,(
% 2.16/0.67    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 2.16/0.67    inference(ennf_transformation,[],[f11])).
% 2.16/0.67  fof(f11,negated_conjecture,(
% 2.16/0.67    ~! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 2.16/0.67    inference(negated_conjecture,[],[f10])).
% 2.16/0.67  fof(f10,conjecture,(
% 2.16/0.67    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).
% 2.16/0.67  % SZS output end Proof for theBenchmark
% 2.16/0.67  % (22969)------------------------------
% 2.16/0.67  % (22969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.67  % (22969)Termination reason: Refutation
% 2.16/0.67  
% 2.16/0.67  % (22969)Memory used [KB]: 8187
% 2.16/0.67  % (22969)Time elapsed: 0.235 s
% 2.16/0.67  % (22969)------------------------------
% 2.16/0.67  % (22969)------------------------------
% 2.16/0.67  % (22958)Success in time 0.309 s
%------------------------------------------------------------------------------
