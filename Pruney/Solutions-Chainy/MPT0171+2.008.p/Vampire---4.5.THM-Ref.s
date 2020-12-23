%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:57 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   25 (  31 expanded)
%              Number of leaves         :    8 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   29 (  36 expanded)
%              Number of equality atoms :   22 (  28 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f26])).

fof(f26,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f25])).

fof(f25,plain,
    ( $false
    | spl1_1 ),
    inference(subsumption_resolution,[],[f23,f19])).

fof(f19,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f14,f13,f17])).

fof(f17,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f15,f16])).

fof(f16,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f15,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f13,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f14,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_enumset1)).

fof(f23,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl1_1
  <=> k1_enumset1(sK0,sK0,sK0) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f24,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f18,f21])).

fof(f18,plain,(
    k1_enumset1(sK0,sK0,sK0) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f11,f12,f17])).

fof(f12,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(f11,plain,(
    k1_tarski(sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k1_tarski(sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).

fof(f9,plain,
    ( ? [X0] : k1_tarski(X0) != k3_enumset1(X0,X0,X0,X0,X0)
   => k1_tarski(sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] : k1_tarski(X0) != k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:54:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.41  % (3051)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.41  % (3051)Refutation found. Thanks to Tanya!
% 0.19/0.41  % SZS status Theorem for theBenchmark
% 0.19/0.41  % SZS output start Proof for theBenchmark
% 0.19/0.41  fof(f27,plain,(
% 0.19/0.41    $false),
% 0.19/0.41    inference(avatar_sat_refutation,[],[f24,f26])).
% 0.19/0.41  fof(f26,plain,(
% 0.19/0.41    spl1_1),
% 0.19/0.41    inference(avatar_contradiction_clause,[],[f25])).
% 0.19/0.41  fof(f25,plain,(
% 0.19/0.41    $false | spl1_1),
% 0.19/0.41    inference(subsumption_resolution,[],[f23,f19])).
% 0.19/0.41  fof(f19,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.19/0.41    inference(definition_unfolding,[],[f14,f13,f17])).
% 0.19/0.41  fof(f17,plain,(
% 0.19/0.41    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.19/0.41    inference(definition_unfolding,[],[f15,f16])).
% 0.19/0.41  fof(f16,plain,(
% 0.19/0.41    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f3])).
% 0.19/0.41  fof(f3,axiom,(
% 0.19/0.41    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.19/0.41  fof(f15,plain,(
% 0.19/0.41    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f2])).
% 0.19/0.41  fof(f2,axiom,(
% 0.19/0.41    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.19/0.41  fof(f13,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f1])).
% 0.19/0.41  fof(f1,axiom,(
% 0.19/0.41    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.41  fof(f14,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f5])).
% 0.19/0.41  fof(f5,axiom,(
% 0.19/0.41    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_enumset1)).
% 0.19/0.41  fof(f23,plain,(
% 0.19/0.41    k1_enumset1(sK0,sK0,sK0) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl1_1),
% 0.19/0.41    inference(avatar_component_clause,[],[f21])).
% 0.19/0.41  fof(f21,plain,(
% 0.19/0.41    spl1_1 <=> k1_enumset1(sK0,sK0,sK0) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.19/0.41  fof(f24,plain,(
% 0.19/0.41    ~spl1_1),
% 0.19/0.41    inference(avatar_split_clause,[],[f18,f21])).
% 0.19/0.41  fof(f18,plain,(
% 0.19/0.41    k1_enumset1(sK0,sK0,sK0) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.19/0.41    inference(definition_unfolding,[],[f11,f12,f17])).
% 0.19/0.42  fof(f12,plain,(
% 0.19/0.42    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,axiom,(
% 0.19/0.42    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).
% 0.19/0.42  fof(f11,plain,(
% 0.19/0.42    k1_tarski(sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.19/0.42    inference(cnf_transformation,[],[f10])).
% 0.19/0.42  fof(f10,plain,(
% 0.19/0.42    k1_tarski(sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).
% 0.19/0.42  fof(f9,plain,(
% 0.19/0.42    ? [X0] : k1_tarski(X0) != k3_enumset1(X0,X0,X0,X0,X0) => k1_tarski(sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f8,plain,(
% 0.19/0.42    ? [X0] : k1_tarski(X0) != k3_enumset1(X0,X0,X0,X0,X0)),
% 0.19/0.42    inference(ennf_transformation,[],[f7])).
% 0.19/0.42  fof(f7,negated_conjecture,(
% 0.19/0.42    ~! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)),
% 0.19/0.42    inference(negated_conjecture,[],[f6])).
% 0.19/0.42  fof(f6,conjecture,(
% 0.19/0.42    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_enumset1)).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (3051)------------------------------
% 0.19/0.42  % (3051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (3051)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (3051)Memory used [KB]: 10490
% 0.19/0.42  % (3051)Time elapsed: 0.004 s
% 0.19/0.42  % (3051)------------------------------
% 0.19/0.42  % (3051)------------------------------
% 0.19/0.42  % (3035)Success in time 0.068 s
%------------------------------------------------------------------------------
