%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:26 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   25 (  51 expanded)
%              Number of leaves         :    7 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   30 (  57 expanded)
%              Number of equality atoms :   22 (  48 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f29])).

fof(f29,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f28])).

fof(f28,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f26,f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X1,X1,X1,X0,X2,X3) ),
    inference(definition_unfolding,[],[f12,f15,f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f13,f14])).

fof(f14,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).

fof(f26,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK1,sK1,sK1,sK0,sK2,sK3)
    | spl4_1 ),
    inference(superposition,[],[f22,f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X2,X3,X1) ),
    inference(definition_unfolding,[],[f11,f15,f15])).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

fof(f22,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK1,sK1,sK1,sK3,sK0,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl4_1
  <=> k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) = k4_enumset1(sK1,sK1,sK1,sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f23,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f16,f20])).

fof(f16,plain,(
    k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK1,sK1,sK1,sK3,sK0,sK2) ),
    inference(definition_unfolding,[],[f10,f15,f15])).

fof(f10,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X0,X2)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X0,X2) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:06:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.42  % (6229)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.42  % (6229)Refutation found. Thanks to Tanya!
% 0.19/0.42  % SZS status Theorem for theBenchmark
% 0.19/0.42  % SZS output start Proof for theBenchmark
% 0.19/0.42  fof(f30,plain,(
% 0.19/0.42    $false),
% 0.19/0.42    inference(avatar_sat_refutation,[],[f23,f29])).
% 0.19/0.42  fof(f29,plain,(
% 0.19/0.42    spl4_1),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f28])).
% 0.19/0.42  fof(f28,plain,(
% 0.19/0.42    $false | spl4_1),
% 0.19/0.42    inference(subsumption_resolution,[],[f26,f18])).
% 0.19/0.42  fof(f18,plain,(
% 0.19/0.42    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X1,X1,X1,X0,X2,X3)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f12,f15,f15])).
% 0.19/0.42  fof(f15,plain,(
% 0.19/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f13,f14])).
% 0.19/0.42  fof(f14,plain,(
% 0.19/0.42    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,axiom,(
% 0.19/0.42    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.19/0.42  fof(f13,plain,(
% 0.19/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f3])).
% 0.19/0.42  fof(f3,axiom,(
% 0.19/0.42    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.19/0.42  fof(f12,plain,(
% 0.19/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f2])).
% 0.19/0.42  fof(f2,axiom,(
% 0.19/0.42    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).
% 0.19/0.42  fof(f26,plain,(
% 0.19/0.42    k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK1,sK1,sK1,sK0,sK2,sK3) | spl4_1),
% 0.19/0.42    inference(superposition,[],[f22,f17])).
% 0.19/0.42  fof(f17,plain,(
% 0.19/0.42    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X2,X3,X1)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f11,f15,f15])).
% 0.19/0.42  fof(f11,plain,(
% 0.19/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f1])).
% 0.19/0.42  fof(f1,axiom,(
% 0.19/0.42    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).
% 0.19/0.42  fof(f22,plain,(
% 0.19/0.42    k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK1,sK1,sK1,sK3,sK0,sK2) | spl4_1),
% 0.19/0.42    inference(avatar_component_clause,[],[f20])).
% 0.19/0.42  fof(f20,plain,(
% 0.19/0.42    spl4_1 <=> k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) = k4_enumset1(sK1,sK1,sK1,sK3,sK0,sK2)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.42  fof(f23,plain,(
% 0.19/0.42    ~spl4_1),
% 0.19/0.42    inference(avatar_split_clause,[],[f16,f20])).
% 0.19/0.42  fof(f16,plain,(
% 0.19/0.42    k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK1,sK1,sK1,sK3,sK0,sK2)),
% 0.19/0.42    inference(definition_unfolding,[],[f10,f15,f15])).
% 0.19/0.42  fof(f10,plain,(
% 0.19/0.42    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2)),
% 0.19/0.42    inference(cnf_transformation,[],[f9])).
% 0.19/0.42  fof(f9,plain,(
% 0.19/0.42    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2)),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).
% 0.19/0.42  fof(f8,plain,(
% 0.19/0.42    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X0,X2) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2)),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f7,plain,(
% 0.19/0.42    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X0,X2)),
% 0.19/0.42    inference(ennf_transformation,[],[f6])).
% 0.19/0.42  fof(f6,negated_conjecture,(
% 0.19/0.42    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)),
% 0.19/0.42    inference(negated_conjecture,[],[f5])).
% 0.19/0.42  fof(f5,conjecture,(
% 0.19/0.42    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_enumset1)).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (6229)------------------------------
% 0.19/0.42  % (6229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (6229)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (6229)Memory used [KB]: 10618
% 0.19/0.42  % (6229)Time elapsed: 0.007 s
% 0.19/0.42  % (6229)------------------------------
% 0.19/0.42  % (6229)------------------------------
% 0.19/0.43  % (6213)Success in time 0.083 s
%------------------------------------------------------------------------------
