%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   21 (  24 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  36 expanded)
%              Number of equality atoms :   17 (  20 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f19,f25,f28])).

fof(f28,plain,(
    spl1_2 ),
    inference(avatar_contradiction_clause,[],[f27])).

fof(f27,plain,
    ( $false
    | spl1_2 ),
    inference(trivial_inequality_removal,[],[f26])).

fof(f26,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | spl1_2 ),
    inference(superposition,[],[f24,f11])).

fof(f11,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

fof(f24,plain,
    ( k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl1_2
  <=> k1_tarski(sK0) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f25,plain,
    ( ~ spl1_2
    | spl1_1 ),
    inference(avatar_split_clause,[],[f20,f16,f22])).

fof(f16,plain,
    ( spl1_1
  <=> k1_tarski(sK0) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f20,plain,
    ( k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl1_1 ),
    inference(superposition,[],[f18,f13])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f18,plain,
    ( k1_tarski(sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f16])).

fof(f19,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f10,f16])).

fof(f10,plain,(
    k1_tarski(sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k1_tarski(sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f8])).

fof(f8,plain,
    ( ? [X0] : k1_tarski(X0) != k3_enumset1(X0,X0,X0,X0,X0)
   => k1_tarski(sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] : k1_tarski(X0) != k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.21/0.34  % CPULimit   : 60
% 0.21/0.34  % WCLimit    : 600
% 0.21/0.34  % DateTime   : Tue Dec  1 10:27:23 EST 2020
% 0.21/0.34  % CPUTime    : 
% 0.21/0.46  % (23066)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.46  % (23066)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f19,f25,f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    spl1_2),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    $false | spl1_2),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    k1_tarski(sK0) != k1_tarski(sK0) | spl1_2),
% 0.21/0.46    inference(superposition,[],[f24,f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0) | spl1_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    spl1_2 <=> k1_tarski(sK0) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ~spl1_2 | spl1_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f20,f16,f22])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    spl1_1 <=> k1_tarski(sK0) = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0) | spl1_1),
% 0.21/0.46    inference(superposition,[],[f18,f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    k1_tarski(sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | spl1_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f16])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ~spl1_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f10,f16])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    k1_tarski(sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    k1_tarski(sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0] : k1_tarski(X0) != k3_enumset1(X0,X0,X0,X0,X0) => k1_tarski(sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ? [X0] : k1_tarski(X0) != k3_enumset1(X0,X0,X0,X0,X0)),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,negated_conjecture,(
% 0.21/0.46    ~! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)),
% 0.21/0.46    inference(negated_conjecture,[],[f5])).
% 0.21/0.46  fof(f5,conjecture,(
% 0.21/0.46    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_enumset1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (23066)------------------------------
% 0.21/0.46  % (23066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (23066)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (23066)Memory used [KB]: 10490
% 0.21/0.46  % (23066)Time elapsed: 0.005 s
% 0.21/0.46  % (23066)------------------------------
% 0.21/0.46  % (23066)------------------------------
% 0.21/0.46  % (23054)Success in time 0.104 s
%------------------------------------------------------------------------------
