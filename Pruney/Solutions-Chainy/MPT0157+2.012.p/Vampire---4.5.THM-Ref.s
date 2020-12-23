%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:45 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 105 expanded)
%              Number of leaves         :   12 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   43 ( 110 expanded)
%              Number of equality atoms :   36 ( 102 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f47])).

fof(f47,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f40])).

fof(f40,plain,
    ( $false
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f36,f39])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k5_xboole_0(k2_enumset1(X2,X2,X2,X3),k4_xboole_0(k2_enumset1(X4,X4,X5,X6),k2_enumset1(X2,X2,X2,X3))),k2_enumset1(X0,X0,X0,X1))) = k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X4,X5,X6),k2_enumset1(X0,X1,X2,X3))) ),
    inference(superposition,[],[f32,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X1,X1,X2,X3),k2_enumset1(X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f20,f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X3,X4),k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f21,f18,f25,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f17,f19])).

fof(f17,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k5_xboole_0(k2_enumset1(X3,X3,X3,X4),k4_xboole_0(k2_enumset1(X5,X5,X6,X7),k2_enumset1(X3,X3,X3,X4))),k2_enumset1(X0,X0,X1,X2))) = k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X3,X4),k2_enumset1(X0,X0,X0,X1))),k4_xboole_0(k2_enumset1(X5,X5,X6,X7),k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X3,X4),k2_enumset1(X0,X0,X0,X1))))) ),
    inference(definition_unfolding,[],[f24,f29,f18,f26,f19])).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k5_xboole_0(k2_enumset1(X3,X3,X3,X4),k4_xboole_0(k2_enumset1(X5,X5,X6,X7),k2_enumset1(X3,X3,X3,X4))),k2_enumset1(X0,X0,X1,X2))) ),
    inference(definition_unfolding,[],[f23,f18,f19,f26])).

fof(f23,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_enumset1)).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).

fof(f36,plain,
    ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k4_xboole_0(k2_enumset1(sK2,sK2,sK3,sK4),k2_enumset1(sK0,sK0,sK0,sK1))) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k4_xboole_0(k2_enumset1(sK2,sK2,sK3,sK4),k2_enumset1(sK0,sK0,sK0,sK1))),k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl5_1
  <=> k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k4_xboole_0(k2_enumset1(sK2,sK2,sK3,sK4),k2_enumset1(sK0,sK0,sK0,sK1))) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k4_xboole_0(k2_enumset1(sK2,sK2,sK3,sK4),k2_enumset1(sK0,sK0,sK0,sK1))),k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f37,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f31,f34])).

fof(f31,plain,(
    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k4_xboole_0(k2_enumset1(sK2,sK2,sK3,sK4),k2_enumset1(sK0,sK0,sK0,sK1))) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k4_xboole_0(k2_enumset1(sK2,sK2,sK3,sK4),k2_enumset1(sK0,sK0,sK0,sK1))),k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f15,f26,f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X4,X5),k2_enumset1(X1,X1,X1,X2))),k2_enumset1(X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f22,f18,f27,f26])).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f16,f25])).

fof(f16,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(f15,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k4_enumset1(X0,X0,X1,X2,X3,X4)
   => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.42  % (10687)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.42  % (10687)Refutation found. Thanks to Tanya!
% 0.19/0.42  % SZS status Theorem for theBenchmark
% 0.19/0.42  % SZS output start Proof for theBenchmark
% 0.19/0.42  fof(f48,plain,(
% 0.19/0.42    $false),
% 0.19/0.42    inference(avatar_sat_refutation,[],[f37,f47])).
% 0.19/0.42  fof(f47,plain,(
% 0.19/0.42    spl5_1),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f40])).
% 0.19/0.42  fof(f40,plain,(
% 0.19/0.42    $false | spl5_1),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f36,f39])).
% 0.19/0.42  fof(f39,plain,(
% 0.19/0.42    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k5_xboole_0(k2_enumset1(X2,X2,X2,X3),k4_xboole_0(k2_enumset1(X4,X4,X5,X6),k2_enumset1(X2,X2,X2,X3))),k2_enumset1(X0,X0,X0,X1))) = k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X4,X5,X6),k2_enumset1(X0,X1,X2,X3)))) )),
% 0.19/0.42    inference(superposition,[],[f32,f30])).
% 0.19/0.42  fof(f30,plain,(
% 0.19/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X1,X1,X2,X3),k2_enumset1(X0,X0,X0,X0)))) )),
% 0.19/0.42    inference(definition_unfolding,[],[f20,f26])).
% 0.19/0.42  fof(f26,plain,(
% 0.19/0.42    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X3,X4),k2_enumset1(X0,X0,X0,X1)))) )),
% 0.19/0.42    inference(definition_unfolding,[],[f21,f18,f25,f19])).
% 0.19/0.42  fof(f19,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f8])).
% 0.19/0.42  fof(f8,axiom,(
% 0.19/0.42    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.42  fof(f25,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f17,f19])).
% 0.19/0.42  fof(f17,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f7])).
% 0.19/0.42  fof(f7,axiom,(
% 0.19/0.42    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.42  fof(f18,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f1])).
% 0.19/0.42  fof(f1,axiom,(
% 0.19/0.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.19/0.42  fof(f21,plain,(
% 0.19/0.42    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f2])).
% 0.19/0.42  fof(f2,axiom,(
% 0.19/0.42    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).
% 0.19/0.42  fof(f20,plain,(
% 0.19/0.42    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f9])).
% 0.19/0.42  fof(f9,axiom,(
% 0.19/0.42    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.19/0.42  fof(f32,plain,(
% 0.19/0.42    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k5_xboole_0(k2_enumset1(X3,X3,X3,X4),k4_xboole_0(k2_enumset1(X5,X5,X6,X7),k2_enumset1(X3,X3,X3,X4))),k2_enumset1(X0,X0,X1,X2))) = k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X3,X4),k2_enumset1(X0,X0,X0,X1))),k4_xboole_0(k2_enumset1(X5,X5,X6,X7),k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k2_enumset1(X2,X2,X3,X4),k2_enumset1(X0,X0,X0,X1)))))) )),
% 0.19/0.42    inference(definition_unfolding,[],[f24,f29,f18,f26,f19])).
% 0.19/0.42  fof(f29,plain,(
% 0.19/0.42    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k5_xboole_0(k2_enumset1(X3,X3,X3,X4),k4_xboole_0(k2_enumset1(X5,X5,X6,X7),k2_enumset1(X3,X3,X3,X4))),k2_enumset1(X0,X0,X1,X2)))) )),
% 0.19/0.42    inference(definition_unfolding,[],[f23,f18,f19,f26])).
% 0.19/0.42  fof(f23,plain,(
% 0.19/0.42    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,axiom,(
% 0.19/0.42    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_enumset1)).
% 0.19/0.42  fof(f24,plain,(
% 0.19/0.42    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f5])).
% 0.19/0.42  fof(f5,axiom,(
% 0.19/0.42    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).
% 0.19/0.42  fof(f36,plain,(
% 0.19/0.42    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k4_xboole_0(k2_enumset1(sK2,sK2,sK3,sK4),k2_enumset1(sK0,sK0,sK0,sK1))) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k4_xboole_0(k2_enumset1(sK2,sK2,sK3,sK4),k2_enumset1(sK0,sK0,sK0,sK1))),k2_enumset1(sK0,sK0,sK0,sK0))) | spl5_1),
% 0.19/0.42    inference(avatar_component_clause,[],[f34])).
% 0.19/0.42  fof(f34,plain,(
% 0.19/0.42    spl5_1 <=> k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k4_xboole_0(k2_enumset1(sK2,sK2,sK3,sK4),k2_enumset1(sK0,sK0,sK0,sK1))) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k4_xboole_0(k2_enumset1(sK2,sK2,sK3,sK4),k2_enumset1(sK0,sK0,sK0,sK1))),k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.42  fof(f37,plain,(
% 0.19/0.42    ~spl5_1),
% 0.19/0.42    inference(avatar_split_clause,[],[f31,f34])).
% 0.19/0.42  fof(f31,plain,(
% 0.19/0.42    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k4_xboole_0(k2_enumset1(sK2,sK2,sK3,sK4),k2_enumset1(sK0,sK0,sK0,sK1))) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k4_xboole_0(k2_enumset1(sK2,sK2,sK3,sK4),k2_enumset1(sK0,sK0,sK0,sK1))),k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.19/0.42    inference(definition_unfolding,[],[f15,f26,f28])).
% 0.19/0.42  fof(f28,plain,(
% 0.19/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X4,X5),k2_enumset1(X1,X1,X1,X2))),k2_enumset1(X0,X0,X0,X0)))) )),
% 0.19/0.42    inference(definition_unfolding,[],[f22,f18,f27,f26])).
% 0.19/0.42  fof(f27,plain,(
% 0.19/0.42    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f16,f25])).
% 0.19/0.42  fof(f16,plain,(
% 0.19/0.42    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f6])).
% 0.19/0.42  fof(f6,axiom,(
% 0.19/0.42    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.42  fof(f22,plain,(
% 0.19/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f3])).
% 0.19/0.42  fof(f3,axiom,(
% 0.19/0.42    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).
% 0.19/0.42  fof(f15,plain,(
% 0.19/0.42    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4)),
% 0.19/0.42    inference(cnf_transformation,[],[f14])).
% 0.19/0.42  fof(f14,plain,(
% 0.19/0.42    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4)),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f12,f13])).
% 0.19/0.42  fof(f13,plain,(
% 0.19/0.42    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k4_enumset1(X0,X0,X1,X2,X3,X4) => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4)),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f12,plain,(
% 0.19/0.42    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.19/0.42    inference(ennf_transformation,[],[f11])).
% 0.19/0.42  fof(f11,negated_conjecture,(
% 0.19/0.42    ~! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.19/0.42    inference(negated_conjecture,[],[f10])).
% 0.19/0.42  fof(f10,conjecture,(
% 0.19/0.42    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (10687)------------------------------
% 0.19/0.42  % (10687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (10687)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (10687)Memory used [KB]: 10618
% 0.19/0.42  % (10687)Time elapsed: 0.006 s
% 0.19/0.42  % (10687)------------------------------
% 0.19/0.42  % (10687)------------------------------
% 0.19/0.43  % (10671)Success in time 0.072 s
%------------------------------------------------------------------------------
