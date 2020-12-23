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
% DateTime   : Thu Dec  3 12:34:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  32 expanded)
%              Number of leaves         :    8 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  50 expanded)
%              Number of equality atoms :   22 (  27 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f19,f47,f64,f86])).

fof(f86,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | spl4_7 ),
    inference(trivial_inequality_removal,[],[f79])).

fof(f79,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3)
    | spl4_7 ),
    inference(superposition,[],[f62,f12])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

fof(f62,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl4_7
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK0,sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f64,plain,
    ( ~ spl4_7
    | spl4_5 ),
    inference(avatar_split_clause,[],[f57,f44,f60])).

fof(f44,plain,
    ( spl4_5
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK2,sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f57,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1)
    | spl4_5 ),
    inference(superposition,[],[f46,f13])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_enumset1)).

fof(f46,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f47,plain,
    ( ~ spl4_5
    | spl4_1 ),
    inference(avatar_split_clause,[],[f25,f16,f44])).

fof(f16,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK2,sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f25,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3)
    | spl4_1 ),
    inference(superposition,[],[f18,f11])).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

fof(f18,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f16])).

fof(f19,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f10,f16])).

fof(f10,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X3,X1,X0)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X3,X1,X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:13:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (10850)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.46  % (10850)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f19,f47,f64,f86])).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    spl4_7),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f85])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    $false | spl4_7),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f79])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3) | spl4_7),
% 0.21/0.46    inference(superposition,[],[f62,f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1) | spl4_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f60])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    spl4_7 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK0,sK3,sK2,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    ~spl4_7 | spl4_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f57,f44,f60])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    spl4_5 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK2,sK1,sK0,sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1) | spl4_5),
% 0.21/0.46    inference(superposition,[],[f46,f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_enumset1)).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3) | spl4_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f44])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ~spl4_5 | spl4_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f25,f16,f44])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK2,sK3,sK1,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3) | spl4_1),
% 0.21/0.46    inference(superposition,[],[f18,f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0) | spl4_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f16])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ~spl4_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f10,f16])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X3,X1,X0) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0)),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X3,X1,X0)),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0)),
% 0.21/0.46    inference(negated_conjecture,[],[f5])).
% 0.21/0.46  fof(f5,conjecture,(
% 0.21/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_enumset1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (10850)------------------------------
% 0.21/0.46  % (10850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (10850)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (10850)Memory used [KB]: 10618
% 0.21/0.46  % (10850)Time elapsed: 0.009 s
% 0.21/0.46  % (10850)------------------------------
% 0.21/0.46  % (10850)------------------------------
% 0.21/0.46  % (10830)Success in time 0.11 s
%------------------------------------------------------------------------------
