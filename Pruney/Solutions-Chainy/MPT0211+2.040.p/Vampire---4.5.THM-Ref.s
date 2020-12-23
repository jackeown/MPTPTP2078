%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  55 expanded)
%              Number of leaves         :   13 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   76 ( 102 expanded)
%              Number of equality atoms :   33 (  46 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f226,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f73,f85,f93,f163,f171,f203,f225])).

fof(f225,plain,
    ( ~ spl3_10
    | ~ spl3_12
    | ~ spl3_16
    | spl3_21 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_16
    | spl3_21 ),
    inference(subsumption_resolution,[],[f210,f212])).

fof(f212,plain,
    ( ! [X4,X2,X3] : k2_enumset1(X2,X4,X3,X2) = k1_enumset1(X2,X4,X3)
    | ~ spl3_12
    | ~ spl3_16 ),
    inference(superposition,[],[f170,f92])).

fof(f92,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_12
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f170,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X1,X0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl3_16
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f210,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK2,sK0)
    | ~ spl3_10
    | spl3_21 ),
    inference(superposition,[],[f202,f84])).

fof(f84,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_10
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f202,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0)
    | spl3_21 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl3_21
  <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK1,sK0,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f203,plain,
    ( ~ spl3_21
    | spl3_1
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f178,f161,f46,f200])).

fof(f46,plain,
    ( spl3_1
  <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f161,plain,
    ( spl3_14
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f178,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0)
    | spl3_1
    | ~ spl3_14 ),
    inference(superposition,[],[f48,f162])).

fof(f162,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f161])).

fof(f48,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f171,plain,
    ( spl3_16
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f122,f83,f71,f169])).

fof(f71,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f122,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X1,X0)
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(superposition,[],[f84,f72])).

fof(f72,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f163,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f38,f161])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f93,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f36,f91])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

fof(f85,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f34,f83])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

fof(f73,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f32,f71])).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
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
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:26:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (16191)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.44  % (16191)Refutation not found, incomplete strategy% (16191)------------------------------
% 0.21/0.44  % (16191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (16185)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.45  % (16191)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (16191)Memory used [KB]: 10618
% 0.21/0.45  % (16191)Time elapsed: 0.045 s
% 0.21/0.45  % (16191)------------------------------
% 0.21/0.45  % (16191)------------------------------
% 0.21/0.45  % (16185)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f226,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f49,f73,f85,f93,f163,f171,f203,f225])).
% 0.21/0.45  fof(f225,plain,(
% 0.21/0.45    ~spl3_10 | ~spl3_12 | ~spl3_16 | spl3_21),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f224])).
% 0.21/0.45  fof(f224,plain,(
% 0.21/0.45    $false | (~spl3_10 | ~spl3_12 | ~spl3_16 | spl3_21)),
% 0.21/0.45    inference(subsumption_resolution,[],[f210,f212])).
% 0.21/0.45  fof(f212,plain,(
% 0.21/0.45    ( ! [X4,X2,X3] : (k2_enumset1(X2,X4,X3,X2) = k1_enumset1(X2,X4,X3)) ) | (~spl3_12 | ~spl3_16)),
% 0.21/0.45    inference(superposition,[],[f170,f92])).
% 0.21/0.45  fof(f92,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) ) | ~spl3_12),
% 0.21/0.45    inference(avatar_component_clause,[],[f91])).
% 0.21/0.45  fof(f91,plain,(
% 0.21/0.45    spl3_12 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.45  fof(f170,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X1,X0)) ) | ~spl3_16),
% 0.21/0.45    inference(avatar_component_clause,[],[f169])).
% 0.21/0.45  fof(f169,plain,(
% 0.21/0.45    spl3_16 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X1,X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.45  fof(f210,plain,(
% 0.21/0.45    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK2,sK0) | (~spl3_10 | spl3_21)),
% 0.21/0.45    inference(superposition,[],[f202,f84])).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) ) | ~spl3_10),
% 0.21/0.45    inference(avatar_component_clause,[],[f83])).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    spl3_10 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.46  fof(f202,plain,(
% 0.21/0.46    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0) | spl3_21),
% 0.21/0.46    inference(avatar_component_clause,[],[f200])).
% 0.21/0.46  fof(f200,plain,(
% 0.21/0.46    spl3_21 <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK1,sK0,sK2,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.46  fof(f203,plain,(
% 0.21/0.46    ~spl3_21 | spl3_1 | ~spl3_14),
% 0.21/0.46    inference(avatar_split_clause,[],[f178,f161,f46,f200])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    spl3_1 <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f161,plain,(
% 0.21/0.46    spl3_14 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.46  fof(f178,plain,(
% 0.21/0.46    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0) | (spl3_1 | ~spl3_14)),
% 0.21/0.46    inference(superposition,[],[f48,f162])).
% 0.21/0.46  fof(f162,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) ) | ~spl3_14),
% 0.21/0.46    inference(avatar_component_clause,[],[f161])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) | spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f46])).
% 0.21/0.46  fof(f171,plain,(
% 0.21/0.46    spl3_16 | ~spl3_7 | ~spl3_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f122,f83,f71,f169])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    spl3_7 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.46  fof(f122,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X1,X0)) ) | (~spl3_7 | ~spl3_10)),
% 0.21/0.46    inference(superposition,[],[f84,f72])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) ) | ~spl3_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f71])).
% 0.21/0.46  fof(f163,plain,(
% 0.21/0.46    spl3_14),
% 0.21/0.46    inference(avatar_split_clause,[],[f38,f161])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 0.21/0.46  fof(f93,plain,(
% 0.21/0.46    spl3_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f36,f91])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    spl3_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f34,f83])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    spl3_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f32,f71])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ~spl3_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f25,f46])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.46    inference(cnf_transformation,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f21])).
% 0.21/0.46  fof(f21,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.21/0.46    inference(negated_conjecture,[],[f20])).
% 0.21/0.46  fof(f20,conjecture,(
% 0.21/0.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (16185)------------------------------
% 0.21/0.46  % (16185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (16185)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (16185)Memory used [KB]: 6268
% 0.21/0.46  % (16185)Time elapsed: 0.061 s
% 0.21/0.46  % (16185)------------------------------
% 0.21/0.46  % (16185)------------------------------
% 0.21/0.46  % (16184)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (16173)Success in time 0.098 s
%------------------------------------------------------------------------------
