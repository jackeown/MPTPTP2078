%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:44 EST 2020

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
fof(f246,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f69,f79,f87,f165,f179,f231,f245])).

fof(f245,plain,
    ( ~ spl3_9
    | ~ spl3_11
    | spl3_16
    | ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | ~ spl3_9
    | ~ spl3_11
    | spl3_16
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f201,f236])).

fof(f236,plain,
    ( ! [X21,X22,X20] : k2_enumset1(X20,X22,X21,X20) = k1_enumset1(X20,X22,X21)
    | ~ spl3_11
    | ~ spl3_21 ),
    inference(superposition,[],[f230,f86])).

fof(f86,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_11
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f230,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X1,X0)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl3_21
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f201,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK2,sK0)
    | ~ spl3_9
    | spl3_16 ),
    inference(superposition,[],[f178,f78])).

fof(f78,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_9
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f178,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl3_16
  <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK1,sK0,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f231,plain,
    ( spl3_21
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f100,f77,f67,f229])).

fof(f67,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f100,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X1,X0)
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(superposition,[],[f78,f68])).

fof(f68,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f179,plain,
    ( ~ spl3_16
    | spl3_1
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f172,f163,f42,f176])).

fof(f42,plain,
    ( spl3_1
  <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f163,plain,
    ( spl3_14
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f172,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0)
    | spl3_1
    | ~ spl3_14 ),
    inference(superposition,[],[f44,f164])).

fof(f164,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f163])).

fof(f44,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f165,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f35,f163])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f87,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f33,f85])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

fof(f79,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f31,f77])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

fof(f69,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f29,f67])).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f45,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f23,f42])).

fof(f23,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:51:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (26935)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (26920)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (26924)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (26922)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (26936)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.47  % (26932)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (26926)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (26925)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (26927)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (26923)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (26934)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (26925)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f246,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f45,f69,f79,f87,f165,f179,f231,f245])).
% 0.21/0.48  fof(f245,plain,(
% 0.21/0.48    ~spl3_9 | ~spl3_11 | spl3_16 | ~spl3_21),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f244])).
% 0.21/0.48  fof(f244,plain,(
% 0.21/0.48    $false | (~spl3_9 | ~spl3_11 | spl3_16 | ~spl3_21)),
% 0.21/0.48    inference(subsumption_resolution,[],[f201,f236])).
% 0.21/0.48  fof(f236,plain,(
% 0.21/0.48    ( ! [X21,X22,X20] : (k2_enumset1(X20,X22,X21,X20) = k1_enumset1(X20,X22,X21)) ) | (~spl3_11 | ~spl3_21)),
% 0.21/0.48    inference(superposition,[],[f230,f86])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) ) | ~spl3_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f85])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl3_11 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.48  fof(f230,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X1,X0)) ) | ~spl3_21),
% 0.21/0.48    inference(avatar_component_clause,[],[f229])).
% 0.21/0.48  fof(f229,plain,(
% 0.21/0.48    spl3_21 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X1,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK2,sK0) | (~spl3_9 | spl3_16)),
% 0.21/0.48    inference(superposition,[],[f178,f78])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) ) | ~spl3_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    spl3_9 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0) | spl3_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f176])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    spl3_16 <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK1,sK0,sK2,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.48  fof(f231,plain,(
% 0.21/0.48    spl3_21 | ~spl3_7 | ~spl3_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f100,f77,f67,f229])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    spl3_7 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X1,X0)) ) | (~spl3_7 | ~spl3_9)),
% 0.21/0.48    inference(superposition,[],[f78,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) ) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f67])).
% 0.21/0.48  fof(f179,plain,(
% 0.21/0.48    ~spl3_16 | spl3_1 | ~spl3_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f172,f163,f42,f176])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    spl3_1 <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    spl3_14 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0) | (spl3_1 | ~spl3_14)),
% 0.21/0.48    inference(superposition,[],[f44,f164])).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) ) | ~spl3_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f163])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) | spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f42])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    spl3_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f35,f163])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    spl3_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f33,f85])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl3_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f77])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f67])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ~spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f23,f42])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.21/0.48    inference(negated_conjecture,[],[f18])).
% 0.21/0.48  fof(f18,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (26925)------------------------------
% 0.21/0.48  % (26925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (26925)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (26925)Memory used [KB]: 6268
% 0.21/0.48  % (26925)Time elapsed: 0.065 s
% 0.21/0.48  % (26925)------------------------------
% 0.21/0.48  % (26925)------------------------------
% 0.21/0.48  % (26919)Success in time 0.124 s
%------------------------------------------------------------------------------
