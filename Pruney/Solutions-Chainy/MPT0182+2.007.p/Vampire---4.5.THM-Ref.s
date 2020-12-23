%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  56 expanded)
%              Number of leaves         :   13 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   76 ( 104 expanded)
%              Number of equality atoms :   33 (  47 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f232,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f51,f55,f67,f75,f85,f223,f231])).

fof(f231,plain,
    ( spl3_1
    | ~ spl3_11
    | ~ spl3_29 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | spl3_1
    | ~ spl3_11
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f42,f227])).

fof(f227,plain,
    ( ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k1_enumset1(X4,X3,X5)
    | ~ spl3_11
    | ~ spl3_29 ),
    inference(superposition,[],[f222,f84])).

fof(f84,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f222,plain,
    ( ! [X4,X2,X3] : k1_enumset1(X2,X3,X4) = k2_xboole_0(k2_tarski(X3,X2),k1_tarski(X4))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl3_29
  <=> ! [X3,X2,X4] : k1_enumset1(X2,X3,X4) = k2_xboole_0(k2_tarski(X3,X2),k1_tarski(X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f42,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_1
  <=> k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f223,plain,
    ( spl3_29
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f105,f83,f49,f221])).

fof(f49,plain,
    ( spl3_3
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f105,plain,
    ( ! [X4,X2,X3] : k1_enumset1(X2,X3,X4) = k2_xboole_0(k2_tarski(X3,X2),k1_tarski(X4))
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(superposition,[],[f84,f50])).

fof(f50,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f85,plain,
    ( spl3_11
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f81,f73,f65,f53,f83])).

fof(f53,plain,
    ( spl3_4
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f65,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f73,plain,
    ( spl3_9
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f81,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f80,f66])).

fof(f66,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f65])).

fof(f80,plain,
    ( ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(superposition,[],[f74,f54])).

fof(f54,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f74,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f73])).

fof(f75,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f30,f73])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f67,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f28,f65])).

fof(f28,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f55,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f25,f53])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f24,f49])).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f43,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f22,f40])).

fof(f22,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2)
   => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (18930)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.44  % (18930)Refutation not found, incomplete strategy% (18930)------------------------------
% 0.21/0.44  % (18930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (18930)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.44  
% 0.21/0.44  % (18930)Memory used [KB]: 10618
% 0.21/0.44  % (18930)Time elapsed: 0.025 s
% 0.21/0.44  % (18930)------------------------------
% 0.21/0.44  % (18930)------------------------------
% 0.21/0.45  % (18918)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (18924)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (18919)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (18929)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (18922)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (18920)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (18927)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (18932)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (18933)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (18931)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (18921)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (18934)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (18925)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (18923)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (18936)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (18923)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f43,f51,f55,f67,f75,f85,f223,f231])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    spl3_1 | ~spl3_11 | ~spl3_29),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f230])).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    $false | (spl3_1 | ~spl3_11 | ~spl3_29)),
% 0.21/0.49    inference(subsumption_resolution,[],[f42,f227])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k1_enumset1(X4,X3,X5)) ) | (~spl3_11 | ~spl3_29)),
% 0.21/0.49    inference(superposition,[],[f222,f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) ) | ~spl3_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    spl3_11 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    ( ! [X4,X2,X3] : (k1_enumset1(X2,X3,X4) = k2_xboole_0(k2_tarski(X3,X2),k1_tarski(X4))) ) | ~spl3_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f221])).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    spl3_29 <=> ! [X3,X2,X4] : k1_enumset1(X2,X3,X4) = k2_xboole_0(k2_tarski(X3,X2),k1_tarski(X4))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) | spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    spl3_1 <=> k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK1,sK0,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    spl3_29 | ~spl3_3 | ~spl3_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f105,f83,f49,f221])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    spl3_3 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ( ! [X4,X2,X3] : (k1_enumset1(X2,X3,X4) = k2_xboole_0(k2_tarski(X3,X2),k1_tarski(X4))) ) | (~spl3_3 | ~spl3_11)),
% 0.21/0.49    inference(superposition,[],[f84,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f49])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl3_11 | ~spl3_4 | ~spl3_7 | ~spl3_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f81,f73,f65,f53,f83])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    spl3_4 <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    spl3_7 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    spl3_9 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) ) | (~spl3_4 | ~spl3_7 | ~spl3_9)),
% 0.21/0.49    inference(forward_demodulation,[],[f80,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) ) | ~spl3_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f65])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) ) | (~spl3_4 | ~spl3_9)),
% 0.21/0.49    inference(superposition,[],[f74,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) ) | ~spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f53])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) ) | ~spl3_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f73])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    spl3_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f30,f73])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl3_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f28,f65])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f25,f53])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f24,f49])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ~spl3_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f22,f40])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2) => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2)),
% 0.21/0.49    inference(ennf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 0.21/0.49    inference(negated_conjecture,[],[f17])).
% 0.21/0.49  fof(f17,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (18923)------------------------------
% 0.21/0.49  % (18923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (18923)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (18923)Memory used [KB]: 6268
% 0.21/0.49  % (18923)Time elapsed: 0.080 s
% 0.21/0.49  % (18923)------------------------------
% 0.21/0.49  % (18923)------------------------------
% 0.21/0.49  % (18914)Success in time 0.132 s
%------------------------------------------------------------------------------
