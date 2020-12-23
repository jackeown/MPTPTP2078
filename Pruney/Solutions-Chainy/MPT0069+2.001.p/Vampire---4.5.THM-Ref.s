%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   33 (  46 expanded)
%              Number of leaves         :    9 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   69 ( 101 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f59,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f20,f24,f28,f39,f49,f58])).

fof(f58,plain,
    ( ~ spl1_1
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(avatar_contradiction_clause,[],[f57])).

fof(f57,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(subsumption_resolution,[],[f51,f27])).

fof(f27,plain,
    ( ! [X0,X1] :
        ( ~ r2_xboole_0(X0,X1)
        | ~ r2_xboole_0(X1,X0) )
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl1_3
  <=> ! [X1,X0] :
        ( ~ r2_xboole_0(X1,X0)
        | ~ r2_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f51,plain,
    ( r2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl1_1
    | ~ spl1_7 ),
    inference(superposition,[],[f19,f48])).

fof(f48,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl1_7
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f19,plain,
    ( r2_xboole_0(sK0,k1_xboole_0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f17])).

fof(f17,plain,
    ( spl1_1
  <=> r2_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f49,plain,
    ( spl1_7
    | ~ spl1_2
    | spl1_5 ),
    inference(avatar_split_clause,[],[f44,f36,f22,f46])).

fof(f22,plain,
    ( spl1_2
  <=> ! [X0] :
        ( r2_xboole_0(k1_xboole_0,X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f36,plain,
    ( spl1_5
  <=> r2_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f44,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_2
    | spl1_5 ),
    inference(resolution,[],[f38,f23])).

fof(f23,plain,
    ( ! [X0] :
        ( r2_xboole_0(k1_xboole_0,X0)
        | k1_xboole_0 = X0 )
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f22])).

fof(f38,plain,
    ( ~ r2_xboole_0(k1_xboole_0,sK0)
    | spl1_5 ),
    inference(avatar_component_clause,[],[f36])).

fof(f39,plain,
    ( ~ spl1_5
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f33,f26,f17,f36])).

fof(f33,plain,
    ( ~ r2_xboole_0(k1_xboole_0,sK0)
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(resolution,[],[f27,f19])).

fof(f28,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f14,f26])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f24,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f13,f22])).

fof(f13,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => r2_xboole_0(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_xboole_1)).

fof(f20,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f12,f17])).

fof(f12,plain,(
    r2_xboole_0(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    r2_xboole_0(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f10])).

fof(f10,plain,
    ( ? [X0] : r2_xboole_0(X0,k1_xboole_0)
   => r2_xboole_0(sK0,k1_xboole_0) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] : r2_xboole_0(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:30:26 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.43  % (4044)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.43  % (4045)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.44  % (4043)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  % (4043)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f20,f24,f28,f39,f49,f58])).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    ~spl1_1 | ~spl1_3 | ~spl1_7),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f57])).
% 0.22/0.44  fof(f57,plain,(
% 0.22/0.44    $false | (~spl1_1 | ~spl1_3 | ~spl1_7)),
% 0.22/0.44    inference(subsumption_resolution,[],[f51,f27])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~r2_xboole_0(X1,X0)) ) | ~spl1_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f26])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    spl1_3 <=> ! [X1,X0] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    r2_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl1_1 | ~spl1_7)),
% 0.22/0.44    inference(superposition,[],[f19,f48])).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    k1_xboole_0 = sK0 | ~spl1_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f46])).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    spl1_7 <=> k1_xboole_0 = sK0),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    r2_xboole_0(sK0,k1_xboole_0) | ~spl1_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    spl1_1 <=> r2_xboole_0(sK0,k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    spl1_7 | ~spl1_2 | spl1_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f44,f36,f22,f46])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    spl1_2 <=> ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    spl1_5 <=> r2_xboole_0(k1_xboole_0,sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    k1_xboole_0 = sK0 | (~spl1_2 | spl1_5)),
% 0.22/0.44    inference(resolution,[],[f38,f23])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ( ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0) ) | ~spl1_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f22])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    ~r2_xboole_0(k1_xboole_0,sK0) | spl1_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f36])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    ~spl1_5 | ~spl1_1 | ~spl1_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f33,f26,f17,f36])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    ~r2_xboole_0(k1_xboole_0,sK0) | (~spl1_1 | ~spl1_3)),
% 0.22/0.44    inference(resolution,[],[f27,f19])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    spl1_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f14,f26])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : (r2_xboole_0(X0,X1) => ~r2_xboole_0(X1,X0))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    spl1_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f13,f22])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ( ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,plain,(
% 0.22/0.44    ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0)),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0] : (k1_xboole_0 != X0 => r2_xboole_0(k1_xboole_0,X0))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_xboole_1)).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    spl1_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f12,f17])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    r2_xboole_0(sK0,k1_xboole_0)),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    r2_xboole_0(sK0,k1_xboole_0)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ? [X0] : r2_xboole_0(X0,k1_xboole_0) => r2_xboole_0(sK0,k1_xboole_0)),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f6,plain,(
% 0.22/0.44    ? [X0] : r2_xboole_0(X0,k1_xboole_0)),
% 0.22/0.44    inference(ennf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,negated_conjecture,(
% 0.22/0.44    ~! [X0] : ~r2_xboole_0(X0,k1_xboole_0)),
% 0.22/0.44    inference(negated_conjecture,[],[f4])).
% 0.22/0.44  fof(f4,conjecture,(
% 0.22/0.44    ! [X0] : ~r2_xboole_0(X0,k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_xboole_1)).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (4043)------------------------------
% 0.22/0.44  % (4043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (4043)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (4043)Memory used [KB]: 10490
% 0.22/0.44  % (4043)Time elapsed: 0.005 s
% 0.22/0.44  % (4043)------------------------------
% 0.22/0.44  % (4043)------------------------------
% 0.22/0.44  % (4037)Success in time 0.076 s
%------------------------------------------------------------------------------
