%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:46 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   47 (  59 expanded)
%              Number of leaves         :   15 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   83 ( 107 expanded)
%              Number of equality atoms :   37 (  49 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f254,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f73,f85,f93,f97,f195,f199,f231,f253])).

fof(f253,plain,
    ( ~ spl3_12
    | ~ spl3_13
    | ~ spl3_16
    | spl3_20 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_16
    | spl3_20 ),
    inference(subsumption_resolution,[],[f234,f240])).

fof(f240,plain,
    ( ! [X14,X15,X16] : k2_enumset1(X15,X16,X15,X14) = k1_enumset1(X15,X14,X16)
    | ~ spl3_12
    | ~ spl3_16 ),
    inference(superposition,[],[f198,f92])).

fof(f92,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_12
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f198,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X1,X0,X0,X2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl3_16
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X1,X0,X0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f234,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK2,sK0,sK1)
    | ~ spl3_13
    | spl3_20 ),
    inference(superposition,[],[f230,f96])).

fof(f96,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_13
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f230,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0)
    | spl3_20 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl3_20
  <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK1,sK0,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f231,plain,
    ( ~ spl3_20
    | spl3_1
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f206,f193,f46,f228])).

fof(f46,plain,
    ( spl3_1
  <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f193,plain,
    ( spl3_15
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f206,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0)
    | spl3_1
    | ~ spl3_15 ),
    inference(superposition,[],[f48,f194])).

fof(f194,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f193])).

fof(f48,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f199,plain,
    ( spl3_16
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f126,f83,f71,f197])).

fof(f71,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f83,plain,
    ( spl3_10
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f126,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X1,X0,X0,X2)
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(superposition,[],[f84,f72])).

fof(f72,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f84,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f83])).

fof(f195,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f39,f193])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f97,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f37,f95])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

fof(f93,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f36,f91])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

fof(f85,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f34,f83])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l129_enumset1)).

fof(f73,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f32,f71])).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f49,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f25,f46])).

fof(f25,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:19:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.44  % (19866)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.44  % (19875)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.45  % (19878)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.46  % (19863)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.46  % (19866)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.46  % SZS output start Proof for theBenchmark
% 0.19/0.46  fof(f254,plain,(
% 0.19/0.46    $false),
% 0.19/0.46    inference(avatar_sat_refutation,[],[f49,f73,f85,f93,f97,f195,f199,f231,f253])).
% 0.19/0.46  fof(f253,plain,(
% 0.19/0.46    ~spl3_12 | ~spl3_13 | ~spl3_16 | spl3_20),
% 0.19/0.46    inference(avatar_contradiction_clause,[],[f252])).
% 0.19/0.46  fof(f252,plain,(
% 0.19/0.46    $false | (~spl3_12 | ~spl3_13 | ~spl3_16 | spl3_20)),
% 0.19/0.46    inference(subsumption_resolution,[],[f234,f240])).
% 0.19/0.46  fof(f240,plain,(
% 0.19/0.46    ( ! [X14,X15,X16] : (k2_enumset1(X15,X16,X15,X14) = k1_enumset1(X15,X14,X16)) ) | (~spl3_12 | ~spl3_16)),
% 0.19/0.46    inference(superposition,[],[f198,f92])).
% 0.19/0.46  fof(f92,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) ) | ~spl3_12),
% 0.19/0.46    inference(avatar_component_clause,[],[f91])).
% 0.19/0.46  fof(f91,plain,(
% 0.19/0.46    spl3_12 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.19/0.46  fof(f198,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X1,X0,X0,X2)) ) | ~spl3_16),
% 0.19/0.46    inference(avatar_component_clause,[],[f197])).
% 0.19/0.46  fof(f197,plain,(
% 0.19/0.46    spl3_16 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X1,X0,X0,X2)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.19/0.46  fof(f234,plain,(
% 0.19/0.46    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK2,sK0,sK1) | (~spl3_13 | spl3_20)),
% 0.19/0.46    inference(superposition,[],[f230,f96])).
% 0.19/0.46  fof(f96,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) ) | ~spl3_13),
% 0.19/0.46    inference(avatar_component_clause,[],[f95])).
% 0.19/0.46  fof(f95,plain,(
% 0.19/0.46    spl3_13 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.19/0.46  fof(f230,plain,(
% 0.19/0.46    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0) | spl3_20),
% 0.19/0.46    inference(avatar_component_clause,[],[f228])).
% 0.19/0.46  fof(f228,plain,(
% 0.19/0.46    spl3_20 <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK1,sK0,sK2,sK0)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.19/0.46  fof(f231,plain,(
% 0.19/0.46    ~spl3_20 | spl3_1 | ~spl3_15),
% 0.19/0.46    inference(avatar_split_clause,[],[f206,f193,f46,f228])).
% 0.19/0.46  fof(f46,plain,(
% 0.19/0.46    spl3_1 <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.46  fof(f193,plain,(
% 0.19/0.46    spl3_15 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.19/0.46  fof(f206,plain,(
% 0.19/0.46    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0) | (spl3_1 | ~spl3_15)),
% 0.19/0.46    inference(superposition,[],[f48,f194])).
% 0.19/0.46  fof(f194,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) ) | ~spl3_15),
% 0.19/0.46    inference(avatar_component_clause,[],[f193])).
% 0.19/0.46  fof(f48,plain,(
% 0.19/0.46    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) | spl3_1),
% 0.19/0.46    inference(avatar_component_clause,[],[f46])).
% 0.19/0.46  fof(f199,plain,(
% 0.19/0.46    spl3_16 | ~spl3_7 | ~spl3_10),
% 0.19/0.46    inference(avatar_split_clause,[],[f126,f83,f71,f197])).
% 0.19/0.46  fof(f71,plain,(
% 0.19/0.46    spl3_7 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.19/0.46  fof(f83,plain,(
% 0.19/0.46    spl3_10 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.19/0.46  fof(f126,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X1,X0,X0,X2)) ) | (~spl3_7 | ~spl3_10)),
% 0.19/0.46    inference(superposition,[],[f84,f72])).
% 0.19/0.46  fof(f72,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) ) | ~spl3_7),
% 0.19/0.46    inference(avatar_component_clause,[],[f71])).
% 0.19/0.46  fof(f84,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)) ) | ~spl3_10),
% 0.19/0.46    inference(avatar_component_clause,[],[f83])).
% 0.19/0.46  fof(f195,plain,(
% 0.19/0.46    spl3_15),
% 0.19/0.46    inference(avatar_split_clause,[],[f39,f193])).
% 0.19/0.46  fof(f39,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f7])).
% 0.19/0.46  fof(f7,axiom,(
% 0.19/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 0.19/0.46  fof(f97,plain,(
% 0.19/0.46    spl3_13),
% 0.19/0.46    inference(avatar_split_clause,[],[f37,f95])).
% 0.19/0.46  fof(f37,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f11])).
% 0.19/0.46  fof(f11,axiom,(
% 0.19/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).
% 0.19/0.46  fof(f93,plain,(
% 0.19/0.46    spl3_12),
% 0.19/0.46    inference(avatar_split_clause,[],[f36,f91])).
% 0.19/0.46  fof(f36,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f10])).
% 0.19/0.46  fof(f10,axiom,(
% 0.19/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).
% 0.19/0.46  fof(f85,plain,(
% 0.19/0.46    spl3_10),
% 0.19/0.46    inference(avatar_split_clause,[],[f34,f83])).
% 0.19/0.46  fof(f34,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f6])).
% 0.19/0.46  fof(f6,axiom,(
% 0.19/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l129_enumset1)).
% 0.19/0.46  fof(f73,plain,(
% 0.19/0.46    spl3_7),
% 0.19/0.46    inference(avatar_split_clause,[],[f32,f71])).
% 0.19/0.46  fof(f32,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f18])).
% 0.19/0.46  fof(f18,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.46  fof(f49,plain,(
% 0.19/0.46    ~spl3_1),
% 0.19/0.46    inference(avatar_split_clause,[],[f25,f46])).
% 0.19/0.46  fof(f25,plain,(
% 0.19/0.46    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.19/0.46    inference(cnf_transformation,[],[f24])).
% 0.19/0.46  fof(f24,plain,(
% 0.19/0.46    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).
% 0.19/0.46  fof(f23,plain,(
% 0.19/0.46    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f22,plain,(
% 0.19/0.46    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.19/0.46    inference(ennf_transformation,[],[f21])).
% 0.19/0.46  fof(f21,negated_conjecture,(
% 0.19/0.46    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.19/0.46    inference(negated_conjecture,[],[f20])).
% 0.19/0.46  fof(f20,conjecture,(
% 0.19/0.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
% 0.19/0.46  % SZS output end Proof for theBenchmark
% 0.19/0.46  % (19866)------------------------------
% 0.19/0.46  % (19866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (19866)Termination reason: Refutation
% 0.19/0.46  
% 0.19/0.46  % (19866)Memory used [KB]: 6268
% 0.19/0.46  % (19866)Time elapsed: 0.060 s
% 0.19/0.46  % (19866)------------------------------
% 0.19/0.46  % (19866)------------------------------
% 0.19/0.46  % (19855)Success in time 0.11 s
%------------------------------------------------------------------------------
