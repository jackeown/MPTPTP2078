%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:32 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   18 (  22 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   28 (  36 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f13,f17,f27])).

fof(f27,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f26])).

fof(f26,plain,
    ( $false
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f20,f16])).

fof(f16,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f15])).

fof(f15,plain,
    ( spl4_2
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f20,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK2,sK3,sK0)
    | spl4_1
    | ~ spl4_2 ),
    inference(superposition,[],[f12,f16])).

fof(f12,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f10])).

fof(f10,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK2,sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f17,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f8,f15])).

fof(f8,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_enumset1)).

fof(f13,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f7,f10])).

fof(f7,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f4,f5])).

fof(f5,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X3,X0,X1)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X3,X0,X1) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X0,X1) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:31:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.39  % (3580)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.13/0.39  % (3580)Refutation found. Thanks to Tanya!
% 0.13/0.39  % SZS status Theorem for theBenchmark
% 0.13/0.39  % SZS output start Proof for theBenchmark
% 0.13/0.39  fof(f28,plain,(
% 0.13/0.39    $false),
% 0.13/0.39    inference(avatar_sat_refutation,[],[f13,f17,f27])).
% 0.13/0.39  fof(f27,plain,(
% 0.13/0.39    spl4_1 | ~spl4_2),
% 0.13/0.39    inference(avatar_contradiction_clause,[],[f26])).
% 0.13/0.39  fof(f26,plain,(
% 0.13/0.39    $false | (spl4_1 | ~spl4_2)),
% 0.13/0.39    inference(subsumption_resolution,[],[f20,f16])).
% 0.13/0.39  fof(f16,plain,(
% 0.13/0.39    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)) ) | ~spl4_2),
% 0.13/0.39    inference(avatar_component_clause,[],[f15])).
% 0.13/0.39  fof(f15,plain,(
% 0.13/0.39    spl4_2 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)),
% 0.13/0.39    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.13/0.39  fof(f20,plain,(
% 0.13/0.39    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK2,sK3,sK0) | (spl4_1 | ~spl4_2)),
% 0.13/0.39    inference(superposition,[],[f12,f16])).
% 0.13/0.39  fof(f12,plain,(
% 0.13/0.39    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK0,sK1) | spl4_1),
% 0.13/0.39    inference(avatar_component_clause,[],[f10])).
% 0.13/0.39  fof(f10,plain,(
% 0.13/0.39    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK2,sK3,sK0,sK1)),
% 0.13/0.39    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.13/0.39  fof(f17,plain,(
% 0.13/0.39    spl4_2),
% 0.13/0.39    inference(avatar_split_clause,[],[f8,f15])).
% 0.13/0.39  fof(f8,plain,(
% 0.13/0.39    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)) )),
% 0.13/0.39    inference(cnf_transformation,[],[f1])).
% 0.13/0.39  fof(f1,axiom,(
% 0.13/0.39    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)),
% 0.13/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_enumset1)).
% 0.13/0.39  fof(f13,plain,(
% 0.13/0.39    ~spl4_1),
% 0.13/0.39    inference(avatar_split_clause,[],[f7,f10])).
% 0.13/0.39  fof(f7,plain,(
% 0.13/0.39    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK0,sK1)),
% 0.13/0.39    inference(cnf_transformation,[],[f6])).
% 0.13/0.39  fof(f6,plain,(
% 0.13/0.39    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK0,sK1)),
% 0.13/0.39    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f4,f5])).
% 0.13/0.39  fof(f5,plain,(
% 0.13/0.39    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X3,X0,X1) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK0,sK1)),
% 0.13/0.39    introduced(choice_axiom,[])).
% 0.13/0.39  fof(f4,plain,(
% 0.13/0.39    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X3,X0,X1)),
% 0.13/0.39    inference(ennf_transformation,[],[f3])).
% 0.13/0.39  fof(f3,negated_conjecture,(
% 0.13/0.39    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X0,X1)),
% 0.13/0.39    inference(negated_conjecture,[],[f2])).
% 0.13/0.39  fof(f2,conjecture,(
% 0.13/0.39    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X0,X1)),
% 0.13/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_enumset1)).
% 0.13/0.39  % SZS output end Proof for theBenchmark
% 0.13/0.39  % (3580)------------------------------
% 0.13/0.39  % (3580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.39  % (3580)Termination reason: Refutation
% 0.13/0.39  
% 0.13/0.39  % (3580)Memory used [KB]: 6012
% 0.13/0.39  % (3580)Time elapsed: 0.002 s
% 0.13/0.39  % (3580)------------------------------
% 0.13/0.39  % (3580)------------------------------
% 0.13/0.39  % (3566)Success in time 0.035 s
%------------------------------------------------------------------------------
