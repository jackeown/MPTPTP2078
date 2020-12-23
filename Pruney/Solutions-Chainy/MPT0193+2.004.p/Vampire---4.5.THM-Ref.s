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
% DateTime   : Thu Dec  3 12:34:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
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
fof(f56,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f15,f19,f23,f55])).

fof(f55,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f54])).

fof(f54,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f39,f18])).

fof(f18,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f17])).

fof(f17,plain,
    ( spl4_2
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f39,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK2,sK0,sK3)
    | spl4_1
    | ~ spl4_3 ),
    inference(superposition,[],[f14,f22])).

fof(f22,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl4_3
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f14,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f12])).

fof(f12,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f23,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f10,f21])).

fof(f10,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

fof(f19,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f9,f17])).

fof(f9,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l123_enumset1)).

fof(f15,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f8,f12])).

fof(f8,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X0,X2)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X0,X2) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:00:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (10683)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (10683)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f56,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f15,f19,f23,f55])).
% 0.22/0.42  fof(f55,plain,(
% 0.22/0.42    spl4_1 | ~spl4_2 | ~spl4_3),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f54])).
% 0.22/0.42  fof(f54,plain,(
% 0.22/0.42    $false | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.22/0.42    inference(subsumption_resolution,[],[f39,f18])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)) ) | ~spl4_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f17])).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    spl4_2 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.42  fof(f39,plain,(
% 0.22/0.42    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK2,sK0,sK3) | (spl4_1 | ~spl4_3)),
% 0.22/0.42    inference(superposition,[],[f14,f22])).
% 0.22/0.42  fof(f22,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) ) | ~spl4_3),
% 0.22/0.42    inference(avatar_component_clause,[],[f21])).
% 0.22/0.42  fof(f21,plain,(
% 0.22/0.42    spl4_3 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2) | spl4_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f12])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK3,sK0,sK2)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    spl4_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f10,f21])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    spl4_2),
% 0.22/0.42    inference(avatar_split_clause,[],[f9,f17])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l123_enumset1)).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    ~spl4_1),
% 0.22/0.42    inference(avatar_split_clause,[],[f8,f12])).
% 0.22/0.42  fof(f8,plain,(
% 0.22/0.42    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2)),
% 0.22/0.42    inference(cnf_transformation,[],[f7])).
% 0.22/0.42  fof(f7,plain,(
% 0.22/0.42    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2)),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).
% 0.22/0.42  fof(f6,plain,(
% 0.22/0.42    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X0,X2) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2)),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f5,plain,(
% 0.22/0.42    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X0,X2)),
% 0.22/0.42    inference(ennf_transformation,[],[f4])).
% 0.22/0.42  fof(f4,negated_conjecture,(
% 0.22/0.42    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)),
% 0.22/0.42    inference(negated_conjecture,[],[f3])).
% 0.22/0.42  fof(f3,conjecture,(
% 0.22/0.42    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_enumset1)).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (10683)------------------------------
% 0.22/0.42  % (10683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (10683)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (10683)Memory used [KB]: 10490
% 0.22/0.42  % (10683)Time elapsed: 0.006 s
% 0.22/0.42  % (10683)------------------------------
% 0.22/0.42  % (10683)------------------------------
% 0.22/0.42  % (10676)Success in time 0.065 s
%------------------------------------------------------------------------------
