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
% DateTime   : Thu Dec  3 12:34:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   27 (  35 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  61 expanded)
%              Number of equality atoms :   21 (  29 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f70,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f15,f19,f23,f31,f69])).

fof(f69,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | ~ spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f67,f22])).

fof(f22,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl4_3
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f67,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK2,sK3,sK0)
    | ~ spl4_3
    | spl4_4 ),
    inference(superposition,[],[f29,f22])).

fof(f29,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK0,sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl4_4
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK2,sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f31,plain,
    ( ~ spl4_4
    | spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f25,f17,f12,f27])).

fof(f12,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK2,sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f17,plain,
    ( spl4_2
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f25,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK0,sK1)
    | spl4_1
    | ~ spl4_2 ),
    inference(superposition,[],[f14,f18])).

fof(f18,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f17])).

fof(f14,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f12])).

fof(f23,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f10,f21])).

fof(f10,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_enumset1)).

fof(f19,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f9,f17])).

fof(f9,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

fof(f15,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f8,f12])).

fof(f8,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X3,X1,X0)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X3,X1,X0) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:07:44 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (16853)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.43  % (16854)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.43  % (16853)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f70,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f15,f19,f23,f31,f69])).
% 0.22/0.43  fof(f69,plain,(
% 0.22/0.43    ~spl4_3 | spl4_4),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f68])).
% 0.22/0.43  fof(f68,plain,(
% 0.22/0.43    $false | (~spl4_3 | spl4_4)),
% 0.22/0.43    inference(subsumption_resolution,[],[f67,f22])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)) ) | ~spl4_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f21])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    spl4_3 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.43  fof(f67,plain,(
% 0.22/0.43    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK2,sK3,sK0) | (~spl4_3 | spl4_4)),
% 0.22/0.43    inference(superposition,[],[f29,f22])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK0,sK1) | spl4_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f27])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    spl4_4 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK2,sK3,sK0,sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    ~spl4_4 | spl4_1 | ~spl4_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f25,f17,f12,f27])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK2,sK3,sK1,sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    spl4_2 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK0,sK1) | (spl4_1 | ~spl4_2)),
% 0.22/0.43    inference(superposition,[],[f14,f18])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) ) | ~spl4_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f17])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0) | spl4_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f12])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    spl4_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f10,f21])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_enumset1)).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    spl4_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f9,f17])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ~spl4_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f8,f12])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,plain,(
% 0.22/0.43    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).
% 0.22/0.43  fof(f6,plain,(
% 0.22/0.43    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X3,X1,X0) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0)),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f5,plain,(
% 0.22/0.43    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X3,X1,X0)),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0)),
% 0.22/0.43    inference(negated_conjecture,[],[f3])).
% 0.22/0.43  fof(f3,conjecture,(
% 0.22/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_enumset1)).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (16853)------------------------------
% 0.22/0.43  % (16853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (16853)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (16853)Memory used [KB]: 10618
% 0.22/0.43  % (16853)Time elapsed: 0.006 s
% 0.22/0.43  % (16853)------------------------------
% 0.22/0.43  % (16853)------------------------------
% 0.22/0.43  % (16845)Success in time 0.064 s
%------------------------------------------------------------------------------
