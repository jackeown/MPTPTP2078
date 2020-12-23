%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 192 expanded)
%              Number of leaves         :   13 (  67 expanded)
%              Depth                    :   19
%              Number of atoms          :   72 ( 209 expanded)
%              Number of equality atoms :   55 ( 187 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1777,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f65,f1742,f1776])).

fof(f1776,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f1772])).

fof(f1772,plain,
    ( $false
    | spl2_4 ),
    inference(unit_resulting_resolution,[],[f27,f1741])).

fof(f1741,plain,
    ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f1739])).

fof(f1739,plain,
    ( spl2_4
  <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f1742,plain,
    ( ~ spl2_4
    | spl2_3 ),
    inference(avatar_split_clause,[],[f1674,f62,f1739])).

fof(f62,plain,
    ( spl2_3
  <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f1674,plain,
    ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_3 ),
    inference(backward_demodulation,[],[f64,f1513])).

fof(f1513,plain,(
    ! [X8,X9] : k2_xboole_0(X8,k4_xboole_0(X8,X9)) = X8 ),
    inference(forward_demodulation,[],[f1512,f81])).

fof(f81,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f74,f16])).

fof(f16,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f74,plain,(
    ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f42,f66])).

fof(f66,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f53,f16])).

fof(f53,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f27,f17])).

fof(f17,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f42,plain,(
    ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f26,f16])).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f15,f23])).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f21,f19])).

fof(f21,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f15,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f1512,plain,(
    ! [X8,X9] : k2_xboole_0(X8,k1_xboole_0) = k2_xboole_0(X8,k4_xboole_0(X8,X9)) ),
    inference(forward_demodulation,[],[f1511,f16])).

fof(f1511,plain,(
    ! [X8,X9] : k2_xboole_0(X8,k4_xboole_0(X8,X9)) = k4_xboole_0(k2_xboole_0(X8,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1510,f66])).

fof(f1510,plain,(
    ! [X8,X9] : k4_xboole_0(k2_xboole_0(X8,k1_xboole_0),k4_xboole_0(X8,X8)) = k2_xboole_0(X8,k4_xboole_0(X8,X9)) ),
    inference(forward_demodulation,[],[f1498,f16])).

fof(f1498,plain,(
    ! [X8,X9] : k2_xboole_0(X8,k4_xboole_0(X8,X9)) = k4_xboole_0(k2_xboole_0(X8,k1_xboole_0),k4_xboole_0(X8,k4_xboole_0(X8,k1_xboole_0))) ),
    inference(superposition,[],[f91,f1299])).

fof(f1299,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(backward_demodulation,[],[f75,f1218])).

fof(f1218,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X2,k4_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f1178,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f18,f23])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f1178,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X2,k4_xboole_0(X3,X2)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2)))) ),
    inference(superposition,[],[f91,f113])).

fof(f113,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f112,f16])).

fof(f112,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f111,f81])).

fof(f111,plain,(
    ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = k2_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f94,f66])).

fof(f94,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f24,f27])).

fof(f75,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(superposition,[],[f66,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f91,plain,(
    ! [X6,X8,X7] : k2_xboole_0(X8,k4_xboole_0(X6,X7)) = k4_xboole_0(k2_xboole_0(X8,k4_xboole_0(X6,k2_xboole_0(X7,X8))),k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k2_xboole_0(X7,X8))))) ),
    inference(superposition,[],[f24,f22])).

fof(f64,plain,
    ( k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f65,plain,
    ( ~ spl2_3
    | spl2_1 ),
    inference(avatar_split_clause,[],[f51,f29,f62])).

fof(f29,plain,
    ( spl2_1
  <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f51,plain,
    ( k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(backward_demodulation,[],[f31,f27])).

fof(f31,plain,
    ( k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f32,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f25,f29])).

fof(f25,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))) ),
    inference(definition_unfolding,[],[f14,f23,f19])).

fof(f14,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:05:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (18101)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.46  % (18094)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (18102)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (18103)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (18104)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (18105)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (18092)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (18096)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (18095)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (18097)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (18099)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (18091)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (18102)Refutation not found, incomplete strategy% (18102)------------------------------
% 0.21/0.48  % (18102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (18102)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (18102)Memory used [KB]: 10490
% 0.21/0.48  % (18102)Time elapsed: 0.058 s
% 0.21/0.48  % (18102)------------------------------
% 0.21/0.48  % (18102)------------------------------
% 0.21/0.49  % (18106)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (18098)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (18093)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (18100)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (18108)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (18107)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (18097)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f1777,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f32,f65,f1742,f1776])).
% 0.21/0.52  fof(f1776,plain,(
% 0.21/0.52    spl2_4),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f1772])).
% 0.21/0.52  fof(f1772,plain,(
% 0.21/0.52    $false | spl2_4),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f27,f1741])).
% 0.21/0.52  fof(f1741,plain,(
% 0.21/0.52    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f1739])).
% 0.21/0.52  fof(f1739,plain,(
% 0.21/0.52    spl2_4 <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f20,f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.52  fof(f1742,plain,(
% 0.21/0.52    ~spl2_4 | spl2_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f1674,f62,f1739])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    spl2_3 <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.52  fof(f1674,plain,(
% 0.21/0.52    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_3),
% 0.21/0.52    inference(backward_demodulation,[],[f64,f1513])).
% 0.21/0.52  fof(f1513,plain,(
% 0.21/0.52    ( ! [X8,X9] : (k2_xboole_0(X8,k4_xboole_0(X8,X9)) = X8) )),
% 0.21/0.52    inference(forward_demodulation,[],[f1512,f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) )),
% 0.21/0.52    inference(superposition,[],[f74,f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X0] : (k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0) )),
% 0.21/0.52    inference(backward_demodulation,[],[f42,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f53,f16])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) )),
% 0.21/0.52    inference(superposition,[],[f27,f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0] : (k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0)) = X0) )),
% 0.21/0.52    inference(forward_demodulation,[],[f26,f16])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X0] : (k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f15,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f21,f19])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.52  fof(f1512,plain,(
% 0.21/0.52    ( ! [X8,X9] : (k2_xboole_0(X8,k1_xboole_0) = k2_xboole_0(X8,k4_xboole_0(X8,X9))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f1511,f16])).
% 0.21/0.52  fof(f1511,plain,(
% 0.21/0.52    ( ! [X8,X9] : (k2_xboole_0(X8,k4_xboole_0(X8,X9)) = k4_xboole_0(k2_xboole_0(X8,k1_xboole_0),k1_xboole_0)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f1510,f66])).
% 0.21/0.52  fof(f1510,plain,(
% 0.21/0.52    ( ! [X8,X9] : (k4_xboole_0(k2_xboole_0(X8,k1_xboole_0),k4_xboole_0(X8,X8)) = k2_xboole_0(X8,k4_xboole_0(X8,X9))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f1498,f16])).
% 0.21/0.52  fof(f1498,plain,(
% 0.21/0.52    ( ! [X8,X9] : (k2_xboole_0(X8,k4_xboole_0(X8,X9)) = k4_xboole_0(k2_xboole_0(X8,k1_xboole_0),k4_xboole_0(X8,k4_xboole_0(X8,k1_xboole_0)))) )),
% 0.21/0.52    inference(superposition,[],[f91,f1299])).
% 0.21/0.52  fof(f1299,plain,(
% 0.21/0.52    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 0.21/0.52    inference(backward_demodulation,[],[f75,f1218])).
% 0.21/0.52  fof(f1218,plain,(
% 0.21/0.52    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X2,k4_xboole_0(X3,X2))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f1178,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f18,f23])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.52  fof(f1178,plain,(
% 0.21/0.52    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X2,k4_xboole_0(X3,X2)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2))))) )),
% 0.21/0.52    inference(superposition,[],[f91,f113])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.52    inference(forward_demodulation,[],[f112,f16])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,X0)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f111,f81])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    ( ! [X0] : (k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = k2_xboole_0(X0,X0)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f94,f66])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ( ! [X0] : (k2_xboole_0(X0,X0) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0))) )),
% 0.21/0.52    inference(superposition,[],[f24,f27])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))) )),
% 0.21/0.52    inference(superposition,[],[f66,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ( ! [X6,X8,X7] : (k2_xboole_0(X8,k4_xboole_0(X6,X7)) = k4_xboole_0(k2_xboole_0(X8,k4_xboole_0(X6,k2_xboole_0(X7,X8))),k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k2_xboole_0(X7,X8)))))) )),
% 0.21/0.52    inference(superposition,[],[f24,f22])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f62])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ~spl2_3 | spl2_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f51,f29,f62])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    spl2_1 <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_1),
% 0.21/0.52    inference(backward_demodulation,[],[f31,f27])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))) | spl2_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f29])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ~spl2_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f25,f29])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))),
% 0.21/0.52    inference(definition_unfolding,[],[f14,f23,f19])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.52    inference(negated_conjecture,[],[f9])).
% 0.21/0.52  fof(f9,conjecture,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (18097)------------------------------
% 0.21/0.52  % (18097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18097)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (18097)Memory used [KB]: 7164
% 0.21/0.52  % (18097)Time elapsed: 0.066 s
% 0.21/0.52  % (18097)------------------------------
% 0.21/0.52  % (18097)------------------------------
% 0.21/0.52  % (18090)Success in time 0.152 s
%------------------------------------------------------------------------------
