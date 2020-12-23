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
% DateTime   : Thu Dec  3 12:34:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
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
fof(f299,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f75,f91,f99,f197,f237,f280,f296])).

fof(f296,plain,
    ( ~ spl3_11
    | ~ spl3_13
    | spl3_20
    | ~ spl3_22 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | ~ spl3_11
    | ~ spl3_13
    | spl3_20
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f257,f285])).

fof(f285,plain,
    ( ! [X21,X22,X20] : k2_enumset1(X20,X22,X21,X20) = k1_enumset1(X20,X22,X21)
    | ~ spl3_13
    | ~ spl3_22 ),
    inference(superposition,[],[f279,f98])).

fof(f98,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl3_13
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f279,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X1,X0)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl3_22
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f257,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK2,sK0)
    | ~ spl3_11
    | spl3_20 ),
    inference(superposition,[],[f236,f90])).

fof(f90,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_11
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f236,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0)
    | spl3_20 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl3_20
  <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK1,sK0,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f280,plain,
    ( spl3_22
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f132,f89,f73,f278])).

fof(f73,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f132,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X1,X0)
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(superposition,[],[f90,f74])).

fof(f74,plain,
    ( ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f237,plain,
    ( ~ spl3_20
    | spl3_1
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f208,f195,f48,f234])).

fof(f48,plain,
    ( spl3_1
  <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f195,plain,
    ( spl3_15
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f208,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0)
    | spl3_1
    | ~ spl3_15 ),
    inference(superposition,[],[f50,f196])).

fof(f196,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f195])).

fof(f50,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f197,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f40,f195])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f99,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f38,f97])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

fof(f91,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f36,f89])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

fof(f75,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f33,f73])).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f51,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f26,f48])).

fof(f26,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:23:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (16591)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (16585)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (16595)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (16596)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (16589)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (16596)Refutation not found, incomplete strategy% (16596)------------------------------
% 0.22/0.48  % (16596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (16596)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (16596)Memory used [KB]: 10618
% 0.22/0.48  % (16596)Time elapsed: 0.061 s
% 0.22/0.48  % (16596)------------------------------
% 0.22/0.48  % (16596)------------------------------
% 0.22/0.49  % (16587)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (16589)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f299,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f51,f75,f91,f99,f197,f237,f280,f296])).
% 0.22/0.49  fof(f296,plain,(
% 0.22/0.49    ~spl3_11 | ~spl3_13 | spl3_20 | ~spl3_22),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f295])).
% 0.22/0.49  fof(f295,plain,(
% 0.22/0.49    $false | (~spl3_11 | ~spl3_13 | spl3_20 | ~spl3_22)),
% 0.22/0.49    inference(subsumption_resolution,[],[f257,f285])).
% 0.22/0.49  fof(f285,plain,(
% 0.22/0.49    ( ! [X21,X22,X20] : (k2_enumset1(X20,X22,X21,X20) = k1_enumset1(X20,X22,X21)) ) | (~spl3_13 | ~spl3_22)),
% 0.22/0.49    inference(superposition,[],[f279,f98])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) ) | ~spl3_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f97])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    spl3_13 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.49  fof(f279,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X1,X0)) ) | ~spl3_22),
% 0.22/0.49    inference(avatar_component_clause,[],[f278])).
% 0.22/0.49  fof(f278,plain,(
% 0.22/0.49    spl3_22 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X1,X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.49  fof(f257,plain,(
% 0.22/0.49    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK2,sK0) | (~spl3_11 | spl3_20)),
% 0.22/0.49    inference(superposition,[],[f236,f90])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) ) | ~spl3_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f89])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    spl3_11 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.49  fof(f236,plain,(
% 0.22/0.49    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0) | spl3_20),
% 0.22/0.49    inference(avatar_component_clause,[],[f234])).
% 0.22/0.49  fof(f234,plain,(
% 0.22/0.49    spl3_20 <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK1,sK0,sK2,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.49  fof(f280,plain,(
% 0.22/0.49    spl3_22 | ~spl3_7 | ~spl3_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f132,f89,f73,f278])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    spl3_7 <=> ! [X1,X0,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X1,X0)) ) | (~spl3_7 | ~spl3_11)),
% 0.22/0.49    inference(superposition,[],[f90,f74])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) ) | ~spl3_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f73])).
% 0.22/0.49  fof(f237,plain,(
% 0.22/0.49    ~spl3_20 | spl3_1 | ~spl3_15),
% 0.22/0.49    inference(avatar_split_clause,[],[f208,f195,f48,f234])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    spl3_1 <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.49  fof(f195,plain,(
% 0.22/0.49    spl3_15 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.49  fof(f208,plain,(
% 0.22/0.49    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0) | (spl3_1 | ~spl3_15)),
% 0.22/0.49    inference(superposition,[],[f50,f196])).
% 0.22/0.49  fof(f196,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) ) | ~spl3_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f195])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) | spl3_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f48])).
% 0.22/0.49  fof(f197,plain,(
% 0.22/0.49    spl3_15),
% 0.22/0.49    inference(avatar_split_clause,[],[f40,f195])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    spl3_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f38,f97])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    spl3_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f36,f89])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    spl3_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f33,f73])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ~spl3_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f26,f48])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.22/0.49    inference(negated_conjecture,[],[f21])).
% 0.22/0.49  fof(f21,conjecture,(
% 0.22/0.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (16589)------------------------------
% 0.22/0.49  % (16589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (16589)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (16589)Memory used [KB]: 6268
% 0.22/0.49  % (16589)Time elapsed: 0.075 s
% 0.22/0.49  % (16589)------------------------------
% 0.22/0.49  % (16589)------------------------------
% 0.22/0.49  % (16583)Success in time 0.133 s
%------------------------------------------------------------------------------
