%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:37 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   23 (  26 expanded)
%              Number of leaves         :    7 (  10 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  43 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f15,f19,f23,f29])).

fof(f29,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f28])).

fof(f28,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f25,f22])).

fof(f22,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl4_3
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f25,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK1,sK2,sK0)
    | spl4_1
    | ~ spl4_2 ),
    inference(superposition,[],[f14,f18])).

fof(f18,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f17])).

fof(f17,plain,
    ( spl4_2
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

% (532)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
fof(f14,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f12])).

fof(f12,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK3,sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f23,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f10,f21])).

fof(f10,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_enumset1)).

fof(f19,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f9,f17])).

fof(f9,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).

fof(f15,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f8,f12])).

fof(f8,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:03:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.41  % (540)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.14/0.41  % (540)Refutation found. Thanks to Tanya!
% 0.14/0.41  % SZS status Theorem for theBenchmark
% 0.14/0.41  % SZS output start Proof for theBenchmark
% 0.14/0.41  fof(f30,plain,(
% 0.14/0.41    $false),
% 0.14/0.41    inference(avatar_sat_refutation,[],[f15,f19,f23,f29])).
% 0.14/0.41  fof(f29,plain,(
% 0.14/0.41    spl4_1 | ~spl4_2 | ~spl4_3),
% 0.14/0.41    inference(avatar_contradiction_clause,[],[f28])).
% 0.14/0.41  fof(f28,plain,(
% 0.14/0.41    $false | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.14/0.41    inference(subsumption_resolution,[],[f25,f22])).
% 0.14/0.41  fof(f22,plain,(
% 0.14/0.41    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0)) ) | ~spl4_3),
% 0.14/0.41    inference(avatar_component_clause,[],[f21])).
% 0.14/0.41  fof(f21,plain,(
% 0.14/0.41    spl4_3 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0)),
% 0.14/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.14/0.41  fof(f25,plain,(
% 0.14/0.41    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK1,sK2,sK0) | (spl4_1 | ~spl4_2)),
% 0.14/0.41    inference(superposition,[],[f14,f18])).
% 0.14/0.41  fof(f18,plain,(
% 0.14/0.41    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)) ) | ~spl4_2),
% 0.14/0.41    inference(avatar_component_clause,[],[f17])).
% 0.14/0.41  fof(f17,plain,(
% 0.14/0.41    spl4_2 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 0.14/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.14/0.41  % (532)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.14/0.41  fof(f14,plain,(
% 0.14/0.41    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) | spl4_1),
% 0.14/0.41    inference(avatar_component_clause,[],[f12])).
% 0.14/0.41  fof(f12,plain,(
% 0.14/0.41    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK3,sK2,sK1,sK0)),
% 0.14/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.14/0.41  fof(f23,plain,(
% 0.14/0.41    spl4_3),
% 0.14/0.41    inference(avatar_split_clause,[],[f10,f21])).
% 0.14/0.41  fof(f10,plain,(
% 0.14/0.41    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0)) )),
% 0.14/0.41    inference(cnf_transformation,[],[f2])).
% 0.14/0.41  fof(f2,axiom,(
% 0.14/0.41    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0)),
% 0.14/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_enumset1)).
% 0.14/0.41  fof(f19,plain,(
% 0.14/0.41    spl4_2),
% 0.14/0.41    inference(avatar_split_clause,[],[f9,f17])).
% 0.14/0.41  fof(f9,plain,(
% 0.14/0.41    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)) )),
% 0.14/0.41    inference(cnf_transformation,[],[f1])).
% 0.14/0.41  fof(f1,axiom,(
% 0.14/0.41    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 0.14/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).
% 0.14/0.41  fof(f15,plain,(
% 0.14/0.41    ~spl4_1),
% 0.14/0.41    inference(avatar_split_clause,[],[f8,f12])).
% 0.14/0.41  fof(f8,plain,(
% 0.14/0.41    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0)),
% 0.14/0.41    inference(cnf_transformation,[],[f7])).
% 0.14/0.41  fof(f7,plain,(
% 0.14/0.41    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0)),
% 0.14/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).
% 0.14/0.41  fof(f6,plain,(
% 0.14/0.41    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0)),
% 0.14/0.41    introduced(choice_axiom,[])).
% 0.14/0.41  fof(f5,plain,(
% 0.14/0.41    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0)),
% 0.14/0.41    inference(ennf_transformation,[],[f4])).
% 0.14/0.41  fof(f4,negated_conjecture,(
% 0.14/0.41    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.14/0.41    inference(negated_conjecture,[],[f3])).
% 0.14/0.41  fof(f3,conjecture,(
% 0.14/0.41    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.14/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).
% 0.14/0.41  % SZS output end Proof for theBenchmark
% 0.14/0.41  % (540)------------------------------
% 0.14/0.41  % (540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.41  % (540)Termination reason: Refutation
% 0.14/0.41  
% 0.14/0.41  % (540)Memory used [KB]: 6012
% 0.14/0.41  % (540)Time elapsed: 0.004 s
% 0.14/0.41  % (540)------------------------------
% 0.14/0.41  % (540)------------------------------
% 0.14/0.41  % (536)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.14/0.41  % (529)Success in time 0.058 s
%------------------------------------------------------------------------------
