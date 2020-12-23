%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  66 expanded)
%              Number of leaves         :   10 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  71 expanded)
%              Number of equality atoms :   30 (  63 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f52])).

fof(f52,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f51])).

fof(f51,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f49,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(X3,k1_enumset1(X1,X1,X2))),k1_enumset1(X0,X0,X0))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(X3,k1_enumset1(X0,X1,X2))) ),
    inference(superposition,[],[f39,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0))) ),
    inference(definition_unfolding,[],[f22,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f24,f21,f20,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f22,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
    inference(definition_unfolding,[],[f23,f21,f21,f21,f21])).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f49,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))),k1_enumset1(sK0,sK0,sK0)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl4_1
  <=> k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))),k1_enumset1(sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f50,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f38,f47])).

fof(f38,plain,(
    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))),k1_enumset1(sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f18,f31,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X1,X1,X2))),k1_enumset1(X0,X0,X0))) ),
    inference(definition_unfolding,[],[f25,f21,f32,f31])).

fof(f32,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f19,f20])).

fof(f19,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f18,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (23314)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.43  % (23314)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f50,f52])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    spl4_1),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f51])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    $false | spl4_1),
% 0.21/0.43    inference(subsumption_resolution,[],[f49,f43])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(X3,k1_enumset1(X1,X1,X2))),k1_enumset1(X0,X0,X0))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(X3,k1_enumset1(X0,X1,X2)))) )),
% 0.21/0.43    inference(superposition,[],[f39,f37])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0)))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f22,f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f24,f21,f20,f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,axiom,(
% 0.21/0.43    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f23,f21,f21,f21,f21])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))),k1_enumset1(sK0,sK0,sK0))) | spl4_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f47])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    spl4_1 <=> k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))),k1_enumset1(sK0,sK0,sK0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    ~spl4_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f38,f47])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))),k1_enumset1(sK0,sK0,sK0)))),
% 0.21/0.43    inference(definition_unfolding,[],[f18,f31,f33])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X1,X1,X2))),k1_enumset1(X0,X0,X0)))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f25,f21,f32,f31])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.43    inference(definition_unfolding,[],[f19,f20])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,axiom,(
% 0.21/0.43    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3)),
% 0.21/0.43    inference(ennf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.21/0.43    inference(negated_conjecture,[],[f13])).
% 0.21/0.43  fof(f13,conjecture,(
% 0.21/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (23314)------------------------------
% 0.21/0.43  % (23314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (23314)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (23314)Memory used [KB]: 10618
% 0.21/0.43  % (23314)Time elapsed: 0.006 s
% 0.21/0.43  % (23314)------------------------------
% 0.21/0.43  % (23314)------------------------------
% 0.21/0.43  % (23298)Success in time 0.078 s
%------------------------------------------------------------------------------
