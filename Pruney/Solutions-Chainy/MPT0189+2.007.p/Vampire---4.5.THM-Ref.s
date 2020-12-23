%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 (  81 expanded)
%              Number of leaves         :   20 (  39 expanded)
%              Depth                    :    6
%              Number of atoms          :  112 ( 150 expanded)
%              Number of equality atoms :   49 (  68 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1167,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f45,f49,f65,f69,f73,f97,f126,f206,f354,f1065,f1166])).

fof(f1166,plain,
    ( spl4_1
    | ~ spl4_19
    | ~ spl4_54 ),
    inference(avatar_contradiction_clause,[],[f1165])).

fof(f1165,plain,
    ( $false
    | spl4_1
    | ~ spl4_19
    | ~ spl4_54 ),
    inference(subsumption_resolution,[],[f40,f1099])).

fof(f1099,plain,
    ( ! [X43,X41,X44,X42] : k2_enumset1(X41,X44,X42,X43) = k2_enumset1(X44,X41,X42,X43)
    | ~ spl4_19
    | ~ spl4_54 ),
    inference(superposition,[],[f1064,f205])).

fof(f205,plain,
    ( ! [X14,X12,X13,X11] : k2_enumset1(X11,X12,X14,X13) = k2_enumset1(X11,X14,X13,X12)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl4_19
  <=> ! [X11,X13,X12,X14] : k2_enumset1(X11,X12,X14,X13) = k2_enumset1(X11,X14,X13,X12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f1064,plain,
    ( ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X5,X6,X7,X4)
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f1063])).

fof(f1063,plain,
    ( spl4_54
  <=> ! [X5,X7,X4,X6] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X5,X6,X7,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f40,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1065,plain,
    ( spl4_54
    | ~ spl4_9
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f355,f352,f71,f1063])).

fof(f71,plain,
    ( spl4_9
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f352,plain,
    ( spl4_30
  <=> ! [X1,X3,X0,X2] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f355,plain,
    ( ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X5,X6,X7,X4)
    | ~ spl4_9
    | ~ spl4_30 ),
    inference(superposition,[],[f353,f72])).

fof(f72,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f71])).

fof(f353,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f352])).

fof(f354,plain,
    ( spl4_30
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f163,f124,f95,f47,f43,f352])).

fof(f43,plain,
    ( spl4_2
  <=> ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f47,plain,
    ( spl4_3
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f95,plain,
    ( spl4_11
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f124,plain,
    ( spl4_15
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f163,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f157,f114])).

fof(f114,plain,
    ( ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X7),k1_enumset1(X4,X5,X6))
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(superposition,[],[f96,f48])).

fof(f48,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f96,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f95])).

fof(f157,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))
    | ~ spl4_2
    | ~ spl4_15 ),
    inference(superposition,[],[f125,f44])).

fof(f44,plain,
    ( ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f125,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f124])).

fof(f206,plain,
    ( spl4_19
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f79,f67,f63,f204])).

fof(f63,plain,
    ( spl4_7
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f67,plain,
    ( spl4_8
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f79,plain,
    ( ! [X14,X12,X13,X11] : k2_enumset1(X11,X12,X14,X13) = k2_enumset1(X11,X14,X13,X12)
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(superposition,[],[f68,f64])).

fof(f64,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f68,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f126,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f34,f124])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(f97,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f31,f95])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f73,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f29,f71])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f69,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f28,f67])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

fof(f65,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

fof(f49,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f23,f47])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f45,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f22,f43])).

fof(f22,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f21,f38])).

fof(f21,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:52:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (17490)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.43  % (17494)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.44  % (17496)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.45  % (17504)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.45  % (17502)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.45  % (17493)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.45  % (17497)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.46  % (17492)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (17503)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.46  % (17499)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.46  % (17491)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (17495)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (17498)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (17501)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (17505)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (17500)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (17500)Refutation not found, incomplete strategy% (17500)------------------------------
% 0.21/0.48  % (17500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (17500)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (17500)Memory used [KB]: 10618
% 0.21/0.48  % (17500)Time elapsed: 0.068 s
% 0.21/0.48  % (17500)------------------------------
% 0.21/0.48  % (17500)------------------------------
% 0.21/0.49  % (17506)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (17494)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f1167,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f41,f45,f49,f65,f69,f73,f97,f126,f206,f354,f1065,f1166])).
% 0.21/0.49  fof(f1166,plain,(
% 0.21/0.49    spl4_1 | ~spl4_19 | ~spl4_54),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f1165])).
% 0.21/0.49  fof(f1165,plain,(
% 0.21/0.49    $false | (spl4_1 | ~spl4_19 | ~spl4_54)),
% 0.21/0.49    inference(subsumption_resolution,[],[f40,f1099])).
% 0.21/0.49  fof(f1099,plain,(
% 0.21/0.49    ( ! [X43,X41,X44,X42] : (k2_enumset1(X41,X44,X42,X43) = k2_enumset1(X44,X41,X42,X43)) ) | (~spl4_19 | ~spl4_54)),
% 0.21/0.49    inference(superposition,[],[f1064,f205])).
% 0.21/0.49  fof(f205,plain,(
% 0.21/0.49    ( ! [X14,X12,X13,X11] : (k2_enumset1(X11,X12,X14,X13) = k2_enumset1(X11,X14,X13,X12)) ) | ~spl4_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f204])).
% 0.21/0.49  fof(f204,plain,(
% 0.21/0.49    spl4_19 <=> ! [X11,X13,X12,X14] : k2_enumset1(X11,X12,X14,X13) = k2_enumset1(X11,X14,X13,X12)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.49  fof(f1064,plain,(
% 0.21/0.49    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X5,X6,X7,X4)) ) | ~spl4_54),
% 0.21/0.49    inference(avatar_component_clause,[],[f1063])).
% 0.21/0.49  fof(f1063,plain,(
% 0.21/0.49    spl4_54 <=> ! [X5,X7,X4,X6] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X5,X6,X7,X4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) | spl4_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK0,sK2,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f1065,plain,(
% 0.21/0.49    spl4_54 | ~spl4_9 | ~spl4_30),
% 0.21/0.49    inference(avatar_split_clause,[],[f355,f352,f71,f1063])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl4_9 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.49  fof(f352,plain,(
% 0.21/0.49    spl4_30 <=> ! [X1,X3,X0,X2] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.49  fof(f355,plain,(
% 0.21/0.49    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X5,X6,X7,X4)) ) | (~spl4_9 | ~spl4_30)),
% 0.21/0.49    inference(superposition,[],[f353,f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) ) | ~spl4_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f71])).
% 0.21/0.49  fof(f353,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)) ) | ~spl4_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f352])).
% 0.21/0.49  fof(f354,plain,(
% 0.21/0.49    spl4_30 | ~spl4_2 | ~spl4_3 | ~spl4_11 | ~spl4_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f163,f124,f95,f47,f43,f352])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    spl4_2 <=> ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    spl4_3 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    spl4_11 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    spl4_15 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)) ) | (~spl4_2 | ~spl4_3 | ~spl4_11 | ~spl4_15)),
% 0.21/0.49    inference(forward_demodulation,[],[f157,f114])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X7),k1_enumset1(X4,X5,X6))) ) | (~spl4_3 | ~spl4_11)),
% 0.21/0.49    inference(superposition,[],[f96,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl4_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f47])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) ) | ~spl4_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f95])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) ) | (~spl4_2 | ~spl4_15)),
% 0.21/0.49    inference(superposition,[],[f125,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) ) | ~spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f43])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) ) | ~spl4_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f124])).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    spl4_19 | ~spl4_7 | ~spl4_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f79,f67,f63,f204])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl4_7 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl4_8 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X14,X12,X13,X11] : (k2_enumset1(X11,X12,X14,X13) = k2_enumset1(X11,X14,X13,X12)) ) | (~spl4_7 | ~spl4_8)),
% 0.21/0.49    inference(superposition,[],[f68,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) ) | ~spl4_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f63])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) ) | ~spl4_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    spl4_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f34,f124])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl4_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f31,f95])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    spl4_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f29,f71])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    spl4_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f28,f67])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    spl4_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f27,f63])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f23,f47])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f22,f43])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ~spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f21,f38])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 0.21/0.49    inference(ennf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 0.21/0.49    inference(negated_conjecture,[],[f16])).
% 0.21/0.49  fof(f16,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (17494)------------------------------
% 0.21/0.49  % (17494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (17494)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (17494)Memory used [KB]: 7164
% 0.21/0.49  % (17494)Time elapsed: 0.098 s
% 0.21/0.49  % (17494)------------------------------
% 0.21/0.49  % (17494)------------------------------
% 0.21/0.49  % (17488)Success in time 0.138 s
%------------------------------------------------------------------------------
