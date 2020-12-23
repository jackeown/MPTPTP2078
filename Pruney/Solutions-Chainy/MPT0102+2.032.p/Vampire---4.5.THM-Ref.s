%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 108 expanded)
%              Number of leaves         :   22 (  53 expanded)
%              Depth                    :    6
%              Number of atoms          :  144 ( 214 expanded)
%              Number of equality atoms :   58 (  93 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f153,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f32,f36,f40,f44,f52,f59,f63,f95,f101,f106,f130,f135,f149])).

fof(f149,plain,
    ( spl2_1
    | ~ spl2_8
    | ~ spl2_18 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl2_1
    | ~ spl2_8
    | ~ spl2_18 ),
    inference(subsumption_resolution,[],[f27,f139])).

fof(f139,plain,
    ( ! [X8,X7] : k3_xboole_0(X7,X8) = k5_xboole_0(k5_xboole_0(X7,X8),k2_xboole_0(X7,X8))
    | ~ spl2_8
    | ~ spl2_18 ),
    inference(superposition,[],[f134,f58])).

fof(f58,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl2_8
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f134,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl2_18
  <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f27,plain,
    ( k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl2_1
  <=> k3_xboole_0(sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f135,plain,
    ( spl2_18
    | ~ spl2_13
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f131,f128,f104,f133])).

fof(f104,plain,
    ( spl2_13
  <=> ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f128,plain,
    ( spl2_17
  <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f131,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1
    | ~ spl2_13
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f129,f105])).

fof(f105,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f104])).

fof(f129,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f128])).

fof(f130,plain,
    ( spl2_17
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f70,f61,f34,f128])).

fof(f34,plain,
    ( spl2_3
  <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f61,plain,
    ( spl2_9
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f70,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(superposition,[],[f62,f35])).

fof(f35,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f62,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f61])).

fof(f106,plain,
    ( spl2_13
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f102,f99,f93,f50,f38,f104])).

fof(f38,plain,
    ( spl2_4
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f50,plain,
    ( spl2_7
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f93,plain,
    ( spl2_11
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f99,plain,
    ( spl2_12
  <=> ! [X0] : k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f102,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f100,f97])).

fof(f97,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f96,f39])).

fof(f39,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f96,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)
    | ~ spl2_7
    | ~ spl2_11 ),
    inference(superposition,[],[f51,f94])).

fof(f94,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f93])).

fof(f51,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f100,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0)) = X0
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f99])).

fof(f101,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f69,f57,f42,f34,f99])).

fof(f42,plain,
    ( spl2_5
  <=> ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f69,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0)) = X0
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f64,f43])).

fof(f43,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f64,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0))
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(superposition,[],[f58,f35])).

fof(f95,plain,
    ( spl2_11
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f55,f50,f38,f30,f93])).

fof(f30,plain,
    ( spl2_2
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f55,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f53,f31])).

fof(f31,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f53,plain,
    ( ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(superposition,[],[f51,f39])).

fof(f63,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f23,f61])).

fof(f23,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f59,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f22,f57])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f52,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f21,f50])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f44,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f19,f42])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f40,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f18,f38])).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f36,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f17,f34])).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f32,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f16,f30])).

fof(f16,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f28,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f15,f25])).

fof(f15,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:35:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.42  % (21668)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.42  % (21668)Refutation not found, incomplete strategy% (21668)------------------------------
% 0.21/0.42  % (21668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (21668)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.42  
% 0.21/0.42  % (21668)Memory used [KB]: 10618
% 0.21/0.42  % (21668)Time elapsed: 0.004 s
% 0.21/0.42  % (21668)------------------------------
% 0.21/0.42  % (21668)------------------------------
% 0.21/0.47  % (21674)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (21660)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (21661)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (21662)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (21659)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  % (21669)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % (21663)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (21670)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (21667)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (21662)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f28,f32,f36,f40,f44,f52,f59,f63,f95,f101,f106,f130,f135,f149])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    spl2_1 | ~spl2_8 | ~spl2_18),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f148])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    $false | (spl2_1 | ~spl2_8 | ~spl2_18)),
% 0.21/0.52    inference(subsumption_resolution,[],[f27,f139])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    ( ! [X8,X7] : (k3_xboole_0(X7,X8) = k5_xboole_0(k5_xboole_0(X7,X8),k2_xboole_0(X7,X8))) ) | (~spl2_8 | ~spl2_18)),
% 0.21/0.52    inference(superposition,[],[f134,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ) | ~spl2_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    spl2_8 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) ) | ~spl2_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f133])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    spl2_18 <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) | spl2_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    spl2_1 <=> k3_xboole_0(sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    spl2_18 | ~spl2_13 | ~spl2_17),
% 0.21/0.52    inference(avatar_split_clause,[],[f131,f128,f104,f133])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    spl2_13 <=> ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    spl2_17 <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) ) | (~spl2_13 | ~spl2_17)),
% 0.21/0.52    inference(forward_demodulation,[],[f129,f105])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl2_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f104])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) ) | ~spl2_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f128])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    spl2_17 | ~spl2_3 | ~spl2_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f70,f61,f34,f128])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    spl2_3 <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    spl2_9 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) ) | (~spl2_3 | ~spl2_9)),
% 0.21/0.52    inference(superposition,[],[f62,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | ~spl2_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f34])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl2_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f61])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    spl2_13 | ~spl2_4 | ~spl2_7 | ~spl2_11 | ~spl2_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f102,f99,f93,f50,f38,f104])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    spl2_4 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    spl2_7 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    spl2_11 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    spl2_12 <=> ! [X0] : k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0)) = X0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl2_4 | ~spl2_7 | ~spl2_11 | ~spl2_12)),
% 0.21/0.52    inference(forward_demodulation,[],[f100,f97])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) ) | (~spl2_4 | ~spl2_7 | ~spl2_11)),
% 0.21/0.52    inference(forward_demodulation,[],[f96,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f38])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)) ) | (~spl2_7 | ~spl2_11)),
% 0.21/0.52    inference(superposition,[],[f51,f94])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl2_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f93])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) ) | ~spl2_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f50])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0)) = X0) ) | ~spl2_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f99])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    spl2_12 | ~spl2_3 | ~spl2_5 | ~spl2_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f69,f57,f42,f34,f99])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    spl2_5 <=> ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0)) = X0) ) | (~spl2_3 | ~spl2_5 | ~spl2_8)),
% 0.21/0.52    inference(forward_demodulation,[],[f64,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | ~spl2_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f42])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0] : (k2_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0))) ) | (~spl2_3 | ~spl2_8)),
% 0.21/0.52    inference(superposition,[],[f58,f35])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    spl2_11 | ~spl2_2 | ~spl2_4 | ~spl2_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f55,f50,f38,f30,f93])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    spl2_2 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl2_2 | ~spl2_4 | ~spl2_7)),
% 0.21/0.52    inference(forward_demodulation,[],[f53,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl2_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f30])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) ) | (~spl2_4 | ~spl2_7)),
% 0.21/0.52    inference(superposition,[],[f51,f39])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    spl2_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f23,f61])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    spl2_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f22,f57])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    spl2_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f21,f50])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    spl2_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f19,f42])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.52    inference(rectify,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    spl2_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f18,f38])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    spl2_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f17,f34])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    spl2_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f16,f30])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ~spl2_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f15,f25])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.21/0.52    inference(negated_conjecture,[],[f9])).
% 0.21/0.52  fof(f9,conjecture,(
% 0.21/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (21662)------------------------------
% 0.21/0.52  % (21662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (21662)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (21662)Memory used [KB]: 6140
% 0.21/0.52  % (21662)Time elapsed: 0.064 s
% 0.21/0.52  % (21662)------------------------------
% 0.21/0.52  % (21662)------------------------------
% 0.21/0.52  % (21656)Success in time 0.16 s
%------------------------------------------------------------------------------
