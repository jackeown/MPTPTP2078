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
% DateTime   : Thu Dec  3 12:34:22 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 113 expanded)
%              Number of leaves         :   20 (  57 expanded)
%              Depth                    :    6
%              Number of atoms          :  135 ( 230 expanded)
%              Number of equality atoms :   52 (  98 expanded)
%              Maximal formula depth    :    7 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f932,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f45,f49,f59,f67,f79,f118,f130,f279,f367,f865,f925,f929,f931])).

fof(f931,plain,
    ( spl4_51
    | ~ spl4_52 ),
    inference(avatar_contradiction_clause,[],[f930])).

fof(f930,plain,
    ( $false
    | spl4_51
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f924,f928])).

fof(f928,plain,
    ( ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X6,X5,X7)
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f927])).

fof(f927,plain,
    ( spl4_52
  <=> ! [X5,X7,X4,X6] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X6,X5,X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f924,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)
    | spl4_51 ),
    inference(avatar_component_clause,[],[f922])).

fof(f922,plain,
    ( spl4_51
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK0,sK2,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f929,plain,
    ( spl4_52
    | ~ spl4_8
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f368,f365,f65,f927])).

fof(f65,plain,
    ( spl4_8
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f365,plain,
    ( spl4_30
  <=> ! [X3,X5,X4,X6] : k3_enumset1(X3,X3,X4,X5,X6) = k2_enumset1(X3,X5,X4,X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f368,plain,
    ( ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X6,X5,X7)
    | ~ spl4_8
    | ~ spl4_30 ),
    inference(superposition,[],[f366,f66])).

fof(f66,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f366,plain,
    ( ! [X6,X4,X5,X3] : k3_enumset1(X3,X3,X4,X5,X6) = k2_enumset1(X3,X5,X4,X6)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f365])).

fof(f925,plain,
    ( ~ spl4_51
    | spl4_1
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f884,f863,f30,f922])).

fof(f30,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f863,plain,
    ( spl4_50
  <=> ! [X5,X7,X4,X6] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X5,X6,X4,X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f884,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)
    | spl4_1
    | ~ spl4_50 ),
    inference(superposition,[],[f32,f864])).

fof(f864,plain,
    ( ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X5,X6,X4,X7)
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f863])).

fof(f32,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f865,plain,
    ( spl4_50
    | ~ spl4_16
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f287,f277,f128,f863])).

fof(f128,plain,
    ( spl4_16
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f277,plain,
    ( spl4_27
  <=> ! [X3,X5,X4,X6] : k2_enumset1(X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X5,X3,X4),k1_tarski(X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f287,plain,
    ( ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X5,X6,X4,X7)
    | ~ spl4_16
    | ~ spl4_27 ),
    inference(superposition,[],[f278,f129])).

fof(f129,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f128])).

fof(f278,plain,
    ( ! [X6,X4,X5,X3] : k2_enumset1(X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X5,X3,X4),k1_tarski(X6))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f277])).

fof(f367,plain,
    ( spl4_30
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f126,f116,f77,f65,f47,f365])).

fof(f47,plain,
    ( spl4_5
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f77,plain,
    ( spl4_10
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f116,plain,
    ( spl4_15
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X2,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f126,plain,
    ( ! [X6,X4,X5,X3] : k3_enumset1(X3,X3,X4,X5,X6) = k2_enumset1(X3,X5,X4,X6)
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f123,f91])).

fof(f91,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f88,f66])).

fof(f88,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(superposition,[],[f78,f48])).

fof(f48,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f78,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f77])).

fof(f123,plain,
    ( ! [X6,X4,X5,X3] : k3_enumset1(X3,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X3,X5,X4),k1_tarski(X6))
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(superposition,[],[f78,f117])).

fof(f117,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X2,X1)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f116])).

fof(f279,plain,
    ( spl4_27
    | ~ spl4_4
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f132,f128,f43,f277])).

fof(f43,plain,
    ( spl4_4
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f132,plain,
    ( ! [X6,X4,X5,X3] : k2_enumset1(X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X5,X3,X4),k1_tarski(X6))
    | ~ spl4_4
    | ~ spl4_16 ),
    inference(superposition,[],[f129,f44])).

fof(f44,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f130,plain,
    ( spl4_16
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f91,f77,f65,f47,f128])).

fof(f118,plain,
    ( spl4_15
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f68,f57,f47,f116])).

fof(f57,plain,
    ( spl4_6
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f68,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X2,X1)
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(superposition,[],[f58,f48])).

fof(f58,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f79,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f25,f77])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(f67,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f23,f65])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f59,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f22,f57])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

fof(f49,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f21,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f45,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f20,f43])).

fof(f20,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

fof(f33,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f17,f30])).

fof(f17,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:57:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (18852)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (18844)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (18841)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (18843)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.51  % (18842)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (18840)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.51  % (18845)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.51  % (18850)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.51  % (18851)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.51  % (18853)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.52  % (18848)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.52  % (18849)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.52  % (18849)Refutation not found, incomplete strategy% (18849)------------------------------
% 0.22/0.52  % (18849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (18849)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (18849)Memory used [KB]: 10618
% 0.22/0.52  % (18849)Time elapsed: 0.083 s
% 0.22/0.52  % (18849)------------------------------
% 0.22/0.52  % (18849)------------------------------
% 1.32/0.55  % (18839)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.53/0.57  % (18855)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.53/0.57  % (18843)Refutation found. Thanks to Tanya!
% 1.53/0.57  % SZS status Theorem for theBenchmark
% 1.53/0.57  % SZS output start Proof for theBenchmark
% 1.53/0.57  fof(f932,plain,(
% 1.53/0.57    $false),
% 1.53/0.57    inference(avatar_sat_refutation,[],[f33,f45,f49,f59,f67,f79,f118,f130,f279,f367,f865,f925,f929,f931])).
% 1.53/0.57  fof(f931,plain,(
% 1.53/0.57    spl4_51 | ~spl4_52),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f930])).
% 1.53/0.57  fof(f930,plain,(
% 1.53/0.57    $false | (spl4_51 | ~spl4_52)),
% 1.53/0.57    inference(subsumption_resolution,[],[f924,f928])).
% 1.53/0.57  fof(f928,plain,(
% 1.53/0.57    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X6,X5,X7)) ) | ~spl4_52),
% 1.53/0.57    inference(avatar_component_clause,[],[f927])).
% 1.53/0.57  fof(f927,plain,(
% 1.53/0.57    spl4_52 <=> ! [X5,X7,X4,X6] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X6,X5,X7)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 1.53/0.57  fof(f924,plain,(
% 1.53/0.57    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) | spl4_51),
% 1.53/0.57    inference(avatar_component_clause,[],[f922])).
% 1.53/0.57  fof(f922,plain,(
% 1.53/0.57    spl4_51 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK0,sK2,sK1,sK3)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 1.53/0.57  fof(f929,plain,(
% 1.53/0.57    spl4_52 | ~spl4_8 | ~spl4_30),
% 1.53/0.57    inference(avatar_split_clause,[],[f368,f365,f65,f927])).
% 1.53/0.57  fof(f65,plain,(
% 1.53/0.57    spl4_8 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.53/0.57  fof(f365,plain,(
% 1.53/0.57    spl4_30 <=> ! [X3,X5,X4,X6] : k3_enumset1(X3,X3,X4,X5,X6) = k2_enumset1(X3,X5,X4,X6)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 1.53/0.57  fof(f368,plain,(
% 1.53/0.57    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X6,X5,X7)) ) | (~spl4_8 | ~spl4_30)),
% 1.53/0.57    inference(superposition,[],[f366,f66])).
% 1.53/0.57  fof(f66,plain,(
% 1.53/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) ) | ~spl4_8),
% 1.53/0.57    inference(avatar_component_clause,[],[f65])).
% 1.53/0.57  fof(f366,plain,(
% 1.53/0.57    ( ! [X6,X4,X5,X3] : (k3_enumset1(X3,X3,X4,X5,X6) = k2_enumset1(X3,X5,X4,X6)) ) | ~spl4_30),
% 1.53/0.57    inference(avatar_component_clause,[],[f365])).
% 1.53/0.57  fof(f925,plain,(
% 1.53/0.57    ~spl4_51 | spl4_1 | ~spl4_50),
% 1.53/0.57    inference(avatar_split_clause,[],[f884,f863,f30,f922])).
% 1.53/0.57  fof(f30,plain,(
% 1.53/0.57    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK0,sK2,sK3)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.53/0.57  fof(f863,plain,(
% 1.53/0.57    spl4_50 <=> ! [X5,X7,X4,X6] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X5,X6,X4,X7)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 1.53/0.57  fof(f884,plain,(
% 1.53/0.57    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) | (spl4_1 | ~spl4_50)),
% 1.53/0.57    inference(superposition,[],[f32,f864])).
% 1.53/0.57  fof(f864,plain,(
% 1.53/0.57    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X5,X6,X4,X7)) ) | ~spl4_50),
% 1.53/0.57    inference(avatar_component_clause,[],[f863])).
% 1.53/0.57  fof(f32,plain,(
% 1.53/0.57    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) | spl4_1),
% 1.53/0.57    inference(avatar_component_clause,[],[f30])).
% 1.53/0.57  fof(f865,plain,(
% 1.53/0.57    spl4_50 | ~spl4_16 | ~spl4_27),
% 1.53/0.57    inference(avatar_split_clause,[],[f287,f277,f128,f863])).
% 1.53/0.57  fof(f128,plain,(
% 1.53/0.57    spl4_16 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.53/0.57  fof(f277,plain,(
% 1.53/0.57    spl4_27 <=> ! [X3,X5,X4,X6] : k2_enumset1(X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X5,X3,X4),k1_tarski(X6))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 1.53/0.57  fof(f287,plain,(
% 1.53/0.57    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X5,X6,X4,X7)) ) | (~spl4_16 | ~spl4_27)),
% 1.53/0.57    inference(superposition,[],[f278,f129])).
% 1.53/0.57  fof(f129,plain,(
% 1.53/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) ) | ~spl4_16),
% 1.53/0.57    inference(avatar_component_clause,[],[f128])).
% 1.53/0.57  fof(f278,plain,(
% 1.53/0.57    ( ! [X6,X4,X5,X3] : (k2_enumset1(X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X5,X3,X4),k1_tarski(X6))) ) | ~spl4_27),
% 1.53/0.57    inference(avatar_component_clause,[],[f277])).
% 1.53/0.57  fof(f367,plain,(
% 1.53/0.57    spl4_30 | ~spl4_5 | ~spl4_8 | ~spl4_10 | ~spl4_15),
% 1.53/0.57    inference(avatar_split_clause,[],[f126,f116,f77,f65,f47,f365])).
% 1.53/0.57  fof(f47,plain,(
% 1.53/0.57    spl4_5 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.53/0.57  fof(f77,plain,(
% 1.53/0.57    spl4_10 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.53/0.57  fof(f116,plain,(
% 1.53/0.57    spl4_15 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X2,X1)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.53/0.57  fof(f126,plain,(
% 1.53/0.57    ( ! [X6,X4,X5,X3] : (k3_enumset1(X3,X3,X4,X5,X6) = k2_enumset1(X3,X5,X4,X6)) ) | (~spl4_5 | ~spl4_8 | ~spl4_10 | ~spl4_15)),
% 1.53/0.57    inference(forward_demodulation,[],[f123,f91])).
% 1.53/0.57  fof(f91,plain,(
% 1.53/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) ) | (~spl4_5 | ~spl4_8 | ~spl4_10)),
% 1.53/0.57    inference(forward_demodulation,[],[f88,f66])).
% 1.53/0.57  fof(f88,plain,(
% 1.53/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) ) | (~spl4_5 | ~spl4_10)),
% 1.53/0.57    inference(superposition,[],[f78,f48])).
% 1.53/0.57  fof(f48,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) ) | ~spl4_5),
% 1.53/0.57    inference(avatar_component_clause,[],[f47])).
% 1.53/0.57  fof(f78,plain,(
% 1.53/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) ) | ~spl4_10),
% 1.53/0.57    inference(avatar_component_clause,[],[f77])).
% 1.53/0.57  fof(f123,plain,(
% 1.53/0.57    ( ! [X6,X4,X5,X3] : (k3_enumset1(X3,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X3,X5,X4),k1_tarski(X6))) ) | (~spl4_10 | ~spl4_15)),
% 1.53/0.57    inference(superposition,[],[f78,f117])).
% 1.53/0.57  fof(f117,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X2,X1)) ) | ~spl4_15),
% 1.53/0.57    inference(avatar_component_clause,[],[f116])).
% 1.53/0.57  fof(f279,plain,(
% 1.53/0.57    spl4_27 | ~spl4_4 | ~spl4_16),
% 1.53/0.57    inference(avatar_split_clause,[],[f132,f128,f43,f277])).
% 1.53/0.57  fof(f43,plain,(
% 1.53/0.57    spl4_4 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.53/0.57  fof(f132,plain,(
% 1.53/0.57    ( ! [X6,X4,X5,X3] : (k2_enumset1(X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X5,X3,X4),k1_tarski(X6))) ) | (~spl4_4 | ~spl4_16)),
% 1.53/0.57    inference(superposition,[],[f129,f44])).
% 1.53/0.57  fof(f44,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) ) | ~spl4_4),
% 1.53/0.57    inference(avatar_component_clause,[],[f43])).
% 1.53/0.57  fof(f130,plain,(
% 1.53/0.57    spl4_16 | ~spl4_5 | ~spl4_8 | ~spl4_10),
% 1.53/0.57    inference(avatar_split_clause,[],[f91,f77,f65,f47,f128])).
% 1.53/0.57  fof(f118,plain,(
% 1.53/0.57    spl4_15 | ~spl4_5 | ~spl4_6),
% 1.53/0.57    inference(avatar_split_clause,[],[f68,f57,f47,f116])).
% 1.53/0.57  fof(f57,plain,(
% 1.53/0.57    spl4_6 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.53/0.57  fof(f68,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X2,X1)) ) | (~spl4_5 | ~spl4_6)),
% 1.53/0.57    inference(superposition,[],[f58,f48])).
% 1.53/0.57  fof(f58,plain,(
% 1.53/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) ) | ~spl4_6),
% 1.53/0.57    inference(avatar_component_clause,[],[f57])).
% 1.53/0.57  fof(f79,plain,(
% 1.53/0.57    spl4_10),
% 1.53/0.57    inference(avatar_split_clause,[],[f25,f77])).
% 1.53/0.57  fof(f25,plain,(
% 1.53/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f3])).
% 1.53/0.57  fof(f3,axiom,(
% 1.53/0.57    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).
% 1.53/0.57  fof(f67,plain,(
% 1.53/0.57    spl4_8),
% 1.53/0.57    inference(avatar_split_clause,[],[f23,f65])).
% 1.53/0.57  fof(f23,plain,(
% 1.53/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f8])).
% 1.53/0.57  fof(f8,axiom,(
% 1.53/0.57    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.53/0.57  fof(f59,plain,(
% 1.53/0.57    spl4_6),
% 1.53/0.57    inference(avatar_split_clause,[],[f22,f57])).
% 1.53/0.57  fof(f22,plain,(
% 1.53/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f2])).
% 1.53/0.57  fof(f2,axiom,(
% 1.53/0.57    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).
% 1.53/0.57  fof(f49,plain,(
% 1.53/0.57    spl4_5),
% 1.53/0.57    inference(avatar_split_clause,[],[f21,f47])).
% 1.53/0.57  fof(f21,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f7])).
% 1.53/0.57  fof(f7,axiom,(
% 1.53/0.57    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.53/0.57  fof(f45,plain,(
% 1.53/0.57    spl4_4),
% 1.53/0.57    inference(avatar_split_clause,[],[f20,f43])).
% 1.53/0.57  fof(f20,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f1])).
% 1.53/0.57  fof(f1,axiom,(
% 1.53/0.57    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).
% 1.53/0.57  fof(f33,plain,(
% 1.53/0.57    ~spl4_1),
% 1.53/0.57    inference(avatar_split_clause,[],[f17,f30])).
% 1.53/0.57  fof(f17,plain,(
% 1.53/0.57    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 1.53/0.57    inference(cnf_transformation,[],[f16])).
% 1.53/0.57  fof(f16,plain,(
% 1.53/0.57    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 1.53/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f15])).
% 1.53/0.57  fof(f15,plain,(
% 1.53/0.57    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 1.53/0.57    introduced(choice_axiom,[])).
% 1.53/0.57  fof(f14,plain,(
% 1.53/0.57    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 1.53/0.57    inference(ennf_transformation,[],[f13])).
% 1.53/0.57  fof(f13,negated_conjecture,(
% 1.53/0.57    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 1.53/0.57    inference(negated_conjecture,[],[f12])).
% 1.53/0.57  fof(f12,conjecture,(
% 1.53/0.57    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).
% 1.53/0.57  % SZS output end Proof for theBenchmark
% 1.53/0.57  % (18843)------------------------------
% 1.53/0.57  % (18843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (18843)Termination reason: Refutation
% 1.53/0.57  
% 1.53/0.57  % (18843)Memory used [KB]: 7036
% 1.53/0.57  % (18843)Time elapsed: 0.119 s
% 1.53/0.57  % (18843)------------------------------
% 1.53/0.57  % (18843)------------------------------
% 1.53/0.57  % (18834)Success in time 0.205 s
%------------------------------------------------------------------------------
