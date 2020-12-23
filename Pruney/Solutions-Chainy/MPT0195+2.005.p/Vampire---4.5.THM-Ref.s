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
% DateTime   : Thu Dec  3 12:34:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   17 (  19 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    6
%              Number of atoms          :   25 (  29 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f13,f17,f19])).

fof(f19,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f18])).

fof(f18,plain,
    ( $false
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f12,f16])).

fof(f16,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f15])).

fof(f15,plain,
    ( spl4_2
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f12,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f10])).

fof(f10,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK2,sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f17,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f8,f15])).

fof(f8,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l129_enumset1)).

fof(f13,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f7,f10])).

fof(f7,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f4,f5])).

fof(f5,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X0,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X0,X3) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_enumset1)).
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
% 0.14/0.34  % DateTime   : Tue Dec  1 10:53:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (6270)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (6270)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f13,f17,f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    spl4_1 | ~spl4_2),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    $false | (spl4_1 | ~spl4_2)),
% 0.21/0.42    inference(subsumption_resolution,[],[f12,f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)) ) | ~spl4_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    spl4_2 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3) | spl4_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK2,sK1,sK0,sK3)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    spl4_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f8,f15])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l129_enumset1)).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ~spl4_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f7,f10])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3)),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,plain,(
% 0.21/0.42    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f4,f5])).
% 0.21/0.42  fof(f5,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X0,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3)),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f4,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X0,X3)),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)),
% 0.21/0.42    inference(negated_conjecture,[],[f2])).
% 0.21/0.42  fof(f2,conjecture,(
% 0.21/0.42    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_enumset1)).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (6270)------------------------------
% 0.21/0.42  % (6270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (6270)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (6270)Memory used [KB]: 10490
% 0.21/0.42  % (6270)Time elapsed: 0.004 s
% 0.21/0.42  % (6270)------------------------------
% 0.21/0.42  % (6270)------------------------------
% 0.21/0.42  % (6264)Success in time 0.062 s
%------------------------------------------------------------------------------
