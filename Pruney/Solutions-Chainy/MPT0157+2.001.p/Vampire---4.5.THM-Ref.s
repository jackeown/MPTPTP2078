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
% DateTime   : Thu Dec  3 12:33:44 EST 2020

% Result     : Theorem 5.15s
% Output     : Refutation 5.15s
% Verified   : 
% Statistics : Number of formulae       :   37 (  81 expanded)
%              Number of leaves         :    9 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :   41 (  86 expanded)
%              Number of equality atoms :   34 (  78 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3133,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f3130])).

fof(f3130,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f3127])).

fof(f3127,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f42,f3126])).

fof(f3126,plain,(
    ! [X163,X161,X164,X162,X160] : k3_enumset1(X160,X161,X162,X163,X164) = k2_xboole_0(k1_tarski(X160),k3_enumset1(X160,X161,X162,X163,X164)) ),
    inference(forward_demodulation,[],[f3125,f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X1,X2,X3,X4)) ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f3125,plain,(
    ! [X163,X161,X164,X162,X160] : k2_xboole_0(k1_tarski(X160),k3_enumset1(X161,X161,X162,X163,X164)) = k2_xboole_0(k1_tarski(X160),k3_enumset1(X160,X161,X162,X163,X164)) ),
    inference(forward_demodulation,[],[f3124,f34])).

fof(f3124,plain,(
    ! [X163,X161,X164,X162,X160] : k2_xboole_0(k1_tarski(X160),k3_enumset1(X160,X161,X162,X163,X164)) = k2_xboole_0(k1_tarski(X160),k2_xboole_0(k1_tarski(X161),k3_enumset1(X161,X161,X162,X163,X164))) ),
    inference(forward_demodulation,[],[f3112,f3106])).

fof(f3106,plain,(
    ! [X134,X132,X130,X133,X131] : k2_xboole_0(k1_tarski(X130),k3_enumset1(X130,X131,X132,X133,X134)) = k2_xboole_0(k3_enumset1(X131,X131,X132,X133,X134),k3_enumset1(X130,X131,X132,X133,X134)) ),
    inference(superposition,[],[f1009,f34])).

fof(f1009,plain,(
    ! [X2,X3] : k2_xboole_0(X3,k2_xboole_0(X3,X2)) = k2_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f729,f712])).

fof(f712,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X2,X1)) = k2_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f44,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f25,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_1)).

fof(f729,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f44,f21])).

fof(f3112,plain,(
    ! [X163,X161,X164,X162,X160] : k2_xboole_0(k1_tarski(X160),k2_xboole_0(k3_enumset1(X161,X161,X162,X163,X164),k3_enumset1(X161,X161,X162,X163,X164))) = k2_xboole_0(k1_tarski(X160),k3_enumset1(X160,X161,X162,X163,X164)) ),
    inference(superposition,[],[f1152,f34])).

fof(f1152,plain,(
    ! [X2,X3] : k2_xboole_0(X3,k2_xboole_0(X3,X2)) = k2_xboole_0(X3,k2_xboole_0(X2,X2)) ),
    inference(superposition,[],[f1009,f48])).

fof(f48,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f24,f21])).

fof(f42,plain,
    ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl5_1
  <=> k3_enumset1(sK0,sK1,sK2,sK3,sK4) = k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f43,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f35,f40])).

fof(f35,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(definition_unfolding,[],[f18,f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(f18,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k4_enumset1(X0,X0,X1,X2,X3,X4)
   => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:39:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.40  % (1653)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (1647)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (1654)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (1640)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (1644)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (1646)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (1643)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (1642)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (1641)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (1651)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (1648)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (1645)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (1651)Refutation not found, incomplete strategy% (1651)------------------------------
% 0.21/0.50  % (1651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1651)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (1651)Memory used [KB]: 10618
% 0.21/0.50  % (1651)Time elapsed: 0.085 s
% 0.21/0.50  % (1651)------------------------------
% 0.21/0.50  % (1651)------------------------------
% 0.21/0.50  % (1657)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (1649)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (1655)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (1650)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (1656)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.52  % (1652)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 5.15/1.01  % (1650)Refutation found. Thanks to Tanya!
% 5.15/1.01  % SZS status Theorem for theBenchmark
% 5.15/1.01  % SZS output start Proof for theBenchmark
% 5.15/1.01  fof(f3133,plain,(
% 5.15/1.01    $false),
% 5.15/1.01    inference(avatar_sat_refutation,[],[f43,f3130])).
% 5.15/1.01  fof(f3130,plain,(
% 5.15/1.01    spl5_1),
% 5.15/1.01    inference(avatar_contradiction_clause,[],[f3127])).
% 5.15/1.01  fof(f3127,plain,(
% 5.15/1.01    $false | spl5_1),
% 5.15/1.01    inference(subsumption_resolution,[],[f42,f3126])).
% 5.15/1.01  fof(f3126,plain,(
% 5.15/1.01    ( ! [X163,X161,X164,X162,X160] : (k3_enumset1(X160,X161,X162,X163,X164) = k2_xboole_0(k1_tarski(X160),k3_enumset1(X160,X161,X162,X163,X164))) )),
% 5.15/1.01    inference(forward_demodulation,[],[f3125,f34])).
% 5.15/1.01  fof(f34,plain,(
% 5.15/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X1,X2,X3,X4))) )),
% 5.15/1.01    inference(definition_unfolding,[],[f27,f26])).
% 5.15/1.01  fof(f26,plain,(
% 5.15/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 5.15/1.01    inference(cnf_transformation,[],[f12])).
% 5.15/1.01  fof(f12,axiom,(
% 5.15/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 5.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 5.15/1.01  fof(f27,plain,(
% 5.15/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 5.15/1.01    inference(cnf_transformation,[],[f5])).
% 5.15/1.01  fof(f5,axiom,(
% 5.15/1.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 5.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 5.15/1.01  fof(f3125,plain,(
% 5.15/1.01    ( ! [X163,X161,X164,X162,X160] : (k2_xboole_0(k1_tarski(X160),k3_enumset1(X161,X161,X162,X163,X164)) = k2_xboole_0(k1_tarski(X160),k3_enumset1(X160,X161,X162,X163,X164))) )),
% 5.15/1.01    inference(forward_demodulation,[],[f3124,f34])).
% 5.15/1.01  fof(f3124,plain,(
% 5.15/1.01    ( ! [X163,X161,X164,X162,X160] : (k2_xboole_0(k1_tarski(X160),k3_enumset1(X160,X161,X162,X163,X164)) = k2_xboole_0(k1_tarski(X160),k2_xboole_0(k1_tarski(X161),k3_enumset1(X161,X161,X162,X163,X164)))) )),
% 5.15/1.01    inference(forward_demodulation,[],[f3112,f3106])).
% 5.15/1.01  fof(f3106,plain,(
% 5.15/1.01    ( ! [X134,X132,X130,X133,X131] : (k2_xboole_0(k1_tarski(X130),k3_enumset1(X130,X131,X132,X133,X134)) = k2_xboole_0(k3_enumset1(X131,X131,X132,X133,X134),k3_enumset1(X130,X131,X132,X133,X134))) )),
% 5.15/1.01    inference(superposition,[],[f1009,f34])).
% 5.15/1.01  fof(f1009,plain,(
% 5.15/1.01    ( ! [X2,X3] : (k2_xboole_0(X3,k2_xboole_0(X3,X2)) = k2_xboole_0(X2,k2_xboole_0(X3,X2))) )),
% 5.15/1.01    inference(superposition,[],[f729,f712])).
% 5.15/1.01  fof(f712,plain,(
% 5.15/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X2,X1)) = k2_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X2,X1))) )),
% 5.15/1.01    inference(superposition,[],[f44,f21])).
% 5.15/1.01  fof(f21,plain,(
% 5.15/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 5.15/1.01    inference(cnf_transformation,[],[f1])).
% 5.15/1.01  fof(f1,axiom,(
% 5.15/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 5.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 5.15/1.01  fof(f44,plain,(
% 5.15/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))) )),
% 5.15/1.01    inference(forward_demodulation,[],[f25,f24])).
% 5.15/1.01  fof(f24,plain,(
% 5.15/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 5.15/1.01    inference(cnf_transformation,[],[f2])).
% 5.15/1.01  fof(f2,axiom,(
% 5.15/1.01    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 5.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 5.15/1.01  fof(f25,plain,(
% 5.15/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))) )),
% 5.15/1.01    inference(cnf_transformation,[],[f3])).
% 5.15/1.01  fof(f3,axiom,(
% 5.15/1.01    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))),
% 5.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_1)).
% 5.15/1.01  fof(f729,plain,(
% 5.15/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X1,X0))) )),
% 5.15/1.01    inference(superposition,[],[f44,f21])).
% 5.15/1.01  fof(f3112,plain,(
% 5.15/1.01    ( ! [X163,X161,X164,X162,X160] : (k2_xboole_0(k1_tarski(X160),k2_xboole_0(k3_enumset1(X161,X161,X162,X163,X164),k3_enumset1(X161,X161,X162,X163,X164))) = k2_xboole_0(k1_tarski(X160),k3_enumset1(X160,X161,X162,X163,X164))) )),
% 5.15/1.01    inference(superposition,[],[f1152,f34])).
% 5.15/1.01  fof(f1152,plain,(
% 5.15/1.01    ( ! [X2,X3] : (k2_xboole_0(X3,k2_xboole_0(X3,X2)) = k2_xboole_0(X3,k2_xboole_0(X2,X2))) )),
% 5.15/1.01    inference(superposition,[],[f1009,f48])).
% 5.15/1.01  fof(f48,plain,(
% 5.15/1.01    ( ! [X4,X5,X3] : (k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4))) )),
% 5.15/1.01    inference(superposition,[],[f24,f21])).
% 5.15/1.01  fof(f42,plain,(
% 5.15/1.01    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) | spl5_1),
% 5.15/1.01    inference(avatar_component_clause,[],[f40])).
% 5.15/1.01  fof(f40,plain,(
% 5.15/1.01    spl5_1 <=> k3_enumset1(sK0,sK1,sK2,sK3,sK4) = k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4))),
% 5.15/1.01    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 5.15/1.01  fof(f43,plain,(
% 5.15/1.01    ~spl5_1),
% 5.15/1.01    inference(avatar_split_clause,[],[f35,f40])).
% 5.15/1.01  fof(f35,plain,(
% 5.15/1.01    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4))),
% 5.15/1.01    inference(definition_unfolding,[],[f18,f30])).
% 5.15/1.01  fof(f30,plain,(
% 5.15/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 5.15/1.01    inference(cnf_transformation,[],[f8])).
% 5.15/1.01  fof(f8,axiom,(
% 5.15/1.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 5.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).
% 5.15/1.01  fof(f18,plain,(
% 5.15/1.01    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4)),
% 5.15/1.01    inference(cnf_transformation,[],[f17])).
% 5.15/1.01  fof(f17,plain,(
% 5.15/1.01    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4)),
% 5.15/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f16])).
% 5.15/1.01  fof(f16,plain,(
% 5.15/1.01    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k4_enumset1(X0,X0,X1,X2,X3,X4) => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4)),
% 5.15/1.01    introduced(choice_axiom,[])).
% 5.15/1.01  fof(f15,plain,(
% 5.15/1.01    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 5.15/1.01    inference(ennf_transformation,[],[f14])).
% 5.15/1.01  fof(f14,negated_conjecture,(
% 5.15/1.01    ~! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 5.15/1.01    inference(negated_conjecture,[],[f13])).
% 5.15/1.01  fof(f13,conjecture,(
% 5.15/1.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 5.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 5.15/1.01  % SZS output end Proof for theBenchmark
% 5.15/1.01  % (1650)------------------------------
% 5.15/1.01  % (1650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.15/1.01  % (1650)Termination reason: Refutation
% 5.15/1.01  
% 5.15/1.01  % (1650)Memory used [KB]: 11001
% 5.15/1.01  % (1650)Time elapsed: 0.588 s
% 5.15/1.01  % (1650)------------------------------
% 5.15/1.01  % (1650)------------------------------
% 5.15/1.01  % (1644)Time limit reached!
% 5.15/1.01  % (1644)------------------------------
% 5.15/1.01  % (1644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.15/1.01  % (1644)Termination reason: Time limit
% 5.15/1.01  
% 5.15/1.01  % (1644)Memory used [KB]: 15351
% 5.15/1.01  % (1644)Time elapsed: 0.603 s
% 5.15/1.01  % (1644)------------------------------
% 5.15/1.01  % (1644)------------------------------
% 5.15/1.02  % (1639)Success in time 0.656 s
%------------------------------------------------------------------------------
