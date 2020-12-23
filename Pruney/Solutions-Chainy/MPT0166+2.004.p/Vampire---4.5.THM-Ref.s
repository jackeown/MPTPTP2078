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
% DateTime   : Thu Dec  3 12:33:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   21 (  24 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  36 expanded)
%              Number of equality atoms :   17 (  20 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f15,f21,f24])).

fof(f24,plain,(
    spl1_2 ),
    inference(avatar_contradiction_clause,[],[f23])).

fof(f23,plain,
    ( $false
    | spl1_2 ),
    inference(trivial_inequality_removal,[],[f22])).

fof(f22,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | spl1_2 ),
    inference(superposition,[],[f20,f9])).

fof(f9,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

fof(f20,plain,
    ( k1_tarski(sK0) != k1_enumset1(sK0,sK0,sK0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl1_2
  <=> k1_tarski(sK0) = k1_enumset1(sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f21,plain,
    ( ~ spl1_2
    | spl1_1 ),
    inference(avatar_split_clause,[],[f16,f12,f18])).

fof(f12,plain,
    ( spl1_1
  <=> k1_tarski(sK0) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f16,plain,
    ( k1_tarski(sK0) != k1_enumset1(sK0,sK0,sK0)
    | spl1_1 ),
    inference(superposition,[],[f14,f10])).

fof(f10,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f14,plain,
    ( k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f12])).

fof(f15,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f8,f12])).

fof(f8,plain,(
    k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f6])).

fof(f6,plain,
    ( ? [X0] : k1_tarski(X0) != k2_enumset1(X0,X0,X0,X0)
   => k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] : k1_tarski(X0) != k2_enumset1(X0,X0,X0,X0) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:01:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.40  % (20344)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.40  % (20344)Refutation found. Thanks to Tanya!
% 0.21/0.40  % SZS status Theorem for theBenchmark
% 0.21/0.40  % SZS output start Proof for theBenchmark
% 0.21/0.40  fof(f25,plain,(
% 0.21/0.40    $false),
% 0.21/0.40    inference(avatar_sat_refutation,[],[f15,f21,f24])).
% 0.21/0.40  fof(f24,plain,(
% 0.21/0.40    spl1_2),
% 0.21/0.40    inference(avatar_contradiction_clause,[],[f23])).
% 0.21/0.40  fof(f23,plain,(
% 0.21/0.40    $false | spl1_2),
% 0.21/0.40    inference(trivial_inequality_removal,[],[f22])).
% 0.21/0.40  fof(f22,plain,(
% 0.21/0.40    k1_tarski(sK0) != k1_tarski(sK0) | spl1_2),
% 0.21/0.40    inference(superposition,[],[f20,f9])).
% 0.21/0.40  fof(f9,plain,(
% 0.21/0.40    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 0.21/0.40    inference(cnf_transformation,[],[f2])).
% 0.21/0.40  fof(f2,axiom,(
% 0.21/0.40    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0)),
% 0.21/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).
% 0.21/0.40  fof(f20,plain,(
% 0.21/0.40    k1_tarski(sK0) != k1_enumset1(sK0,sK0,sK0) | spl1_2),
% 0.21/0.40    inference(avatar_component_clause,[],[f18])).
% 0.21/0.40  fof(f18,plain,(
% 0.21/0.40    spl1_2 <=> k1_tarski(sK0) = k1_enumset1(sK0,sK0,sK0)),
% 0.21/0.40    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.40  fof(f21,plain,(
% 0.21/0.40    ~spl1_2 | spl1_1),
% 0.21/0.40    inference(avatar_split_clause,[],[f16,f12,f18])).
% 0.21/0.40  fof(f12,plain,(
% 0.21/0.40    spl1_1 <=> k1_tarski(sK0) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.40    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.40  fof(f16,plain,(
% 0.21/0.40    k1_tarski(sK0) != k1_enumset1(sK0,sK0,sK0) | spl1_1),
% 0.21/0.40    inference(superposition,[],[f14,f10])).
% 0.21/0.40  fof(f10,plain,(
% 0.21/0.40    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.40    inference(cnf_transformation,[],[f1])).
% 0.21/0.40  fof(f1,axiom,(
% 0.21/0.40    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.40  fof(f14,plain,(
% 0.21/0.40    k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0) | spl1_1),
% 0.21/0.40    inference(avatar_component_clause,[],[f12])).
% 0.21/0.40  fof(f15,plain,(
% 0.21/0.40    ~spl1_1),
% 0.21/0.40    inference(avatar_split_clause,[],[f8,f12])).
% 0.21/0.40  fof(f8,plain,(
% 0.21/0.40    k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.40    inference(cnf_transformation,[],[f7])).
% 0.21/0.40  fof(f7,plain,(
% 0.21/0.40    k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f6])).
% 0.21/0.40  fof(f6,plain,(
% 0.21/0.40    ? [X0] : k1_tarski(X0) != k2_enumset1(X0,X0,X0,X0) => k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.40    introduced(choice_axiom,[])).
% 0.21/0.40  fof(f5,plain,(
% 0.21/0.40    ? [X0] : k1_tarski(X0) != k2_enumset1(X0,X0,X0,X0)),
% 0.21/0.40    inference(ennf_transformation,[],[f4])).
% 0.21/0.40  fof(f4,negated_conjecture,(
% 0.21/0.40    ~! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)),
% 0.21/0.40    inference(negated_conjecture,[],[f3])).
% 0.21/0.40  fof(f3,conjecture,(
% 0.21/0.40    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)),
% 0.21/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).
% 0.21/0.40  % SZS output end Proof for theBenchmark
% 0.21/0.40  % (20344)------------------------------
% 0.21/0.40  % (20344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.40  % (20344)Termination reason: Refutation
% 0.21/0.40  
% 0.21/0.40  % (20344)Memory used [KB]: 10490
% 0.21/0.40  % (20344)Time elapsed: 0.003 s
% 0.21/0.40  % (20344)------------------------------
% 0.21/0.40  % (20344)------------------------------
% 0.21/0.41  % (20332)Success in time 0.056 s
%------------------------------------------------------------------------------
