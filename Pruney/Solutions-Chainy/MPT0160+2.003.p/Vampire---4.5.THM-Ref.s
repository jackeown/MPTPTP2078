%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   26 (  32 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :   42 (  54 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f35,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f15,f19,f23,f29,f34])).

fof(f34,plain,
    ( ~ spl1_2
    | spl1_4 ),
    inference(avatar_contradiction_clause,[],[f30])).

fof(f30,plain,
    ( $false
    | ~ spl1_2
    | spl1_4 ),
    inference(unit_resulting_resolution,[],[f18,f28])).

fof(f28,plain,
    ( k1_tarski(sK0) != k2_tarski(sK0,sK0)
    | spl1_4 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl1_4
  <=> k1_tarski(sK0) = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f18,plain,
    ( ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f17])).

fof(f17,plain,
    ( spl1_2
  <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f29,plain,
    ( ~ spl1_4
    | spl1_1
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f24,f21,f12,f26])).

fof(f12,plain,
    ( spl1_1
  <=> k1_tarski(sK0) = k1_enumset1(sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f21,plain,
    ( spl1_3
  <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f24,plain,
    ( k1_tarski(sK0) != k2_tarski(sK0,sK0)
    | spl1_1
    | ~ spl1_3 ),
    inference(superposition,[],[f14,f22])).

fof(f22,plain,
    ( ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f21])).

fof(f14,plain,
    ( k1_tarski(sK0) != k1_enumset1(sK0,sK0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f12])).

fof(f23,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f10,f21])).

fof(f10,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f19,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f9,f17])).

fof(f9,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f15,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f8,f12])).

fof(f8,plain,(
    k1_tarski(sK0) != k1_enumset1(sK0,sK0,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k1_tarski(sK0) != k1_enumset1(sK0,sK0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f6])).

fof(f6,plain,
    ( ? [X0] : k1_tarski(X0) != k1_enumset1(X0,X0,X0)
   => k1_tarski(sK0) != k1_enumset1(sK0,sK0,sK0) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] : k1_tarski(X0) != k1_enumset1(X0,X0,X0) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:09:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (28925)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (28933)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.45  % (28925)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f15,f19,f23,f29,f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ~spl1_2 | spl1_4),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    $false | (~spl1_2 | spl1_4)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f18,f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    k1_tarski(sK0) != k2_tarski(sK0,sK0) | spl1_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    spl1_4 <=> k1_tarski(sK0) = k2_tarski(sK0,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) ) | ~spl1_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    spl1_2 <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ~spl1_4 | spl1_1 | ~spl1_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f24,f21,f12,f26])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    spl1_1 <=> k1_tarski(sK0) = k1_enumset1(sK0,sK0,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    spl1_3 <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    k1_tarski(sK0) != k2_tarski(sK0,sK0) | (spl1_1 | ~spl1_3)),
% 0.20/0.46    inference(superposition,[],[f14,f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) ) | ~spl1_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f21])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    k1_tarski(sK0) != k1_enumset1(sK0,sK0,sK0) | spl1_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f12])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    spl1_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f10,f21])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    spl1_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f9,f17])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ~spl1_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f8,f12])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    k1_tarski(sK0) != k1_enumset1(sK0,sK0,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    k1_tarski(sK0) != k1_enumset1(sK0,sK0,sK0)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f6])).
% 0.20/0.46  fof(f6,plain,(
% 0.20/0.46    ? [X0] : k1_tarski(X0) != k1_enumset1(X0,X0,X0) => k1_tarski(sK0) != k1_enumset1(sK0,sK0,sK0)),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f5,plain,(
% 0.20/0.46    ? [X0] : k1_tarski(X0) != k1_enumset1(X0,X0,X0)),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,negated_conjecture,(
% 0.20/0.46    ~! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0)),
% 0.20/0.46    inference(negated_conjecture,[],[f3])).
% 0.20/0.46  fof(f3,conjecture,(
% 0.20/0.46    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (28925)------------------------------
% 0.20/0.46  % (28925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (28925)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (28925)Memory used [KB]: 6012
% 0.20/0.46  % (28925)Time elapsed: 0.050 s
% 0.20/0.46  % (28925)------------------------------
% 0.20/0.46  % (28925)------------------------------
% 0.20/0.46  % (28919)Success in time 0.101 s
%------------------------------------------------------------------------------
