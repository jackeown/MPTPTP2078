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
% DateTime   : Thu Dec  3 12:33:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   25 (  28 expanded)
%              Number of leaves         :    8 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   29 (  33 expanded)
%              Number of equality atoms :   22 (  25 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f33,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f32])).

fof(f32,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f31])).

fof(f31,plain,
    ( $false
    | spl7_1 ),
    inference(subsumption_resolution,[],[f29,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f29,plain,
    ( k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)))) != k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_xboole_0(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl7_1
  <=> k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)))) = k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_xboole_0(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f30,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f21,f27])).

fof(f21,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)))) != k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_xboole_0(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6))) ),
    inference(definition_unfolding,[],[f12,f20,f13,f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f13,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f20,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k2_tarski(X3,X4),k2_tarski(X5,X6)))) ),
    inference(definition_unfolding,[],[f17,f19])).

fof(f19,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))) ),
    inference(definition_unfolding,[],[f16,f15])).

fof(f16,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f17,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

fof(f12,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:34:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.44  % (27922)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.44  % (27922)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f30,f32])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    spl7_1),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f31])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    $false | spl7_1),
% 0.22/0.44    inference(subsumption_resolution,[],[f29,f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)))) != k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_xboole_0(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6))) | spl7_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f27])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    spl7_1 <=> k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)))) = k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_xboole_0(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ~spl7_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f21,f27])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)))) != k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_xboole_0(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)))),
% 0.22/0.44    inference(definition_unfolding,[],[f12,f20,f13,f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k2_tarski(X3,X4),k2_tarski(X5,X6))))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f17,f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f16,f15])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6))),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6))),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f9,f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.22/0.44    inference(ennf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.22/0.44    inference(negated_conjecture,[],[f7])).
% 0.22/0.44  fof(f7,conjecture,(
% 0.22/0.44    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (27922)------------------------------
% 0.22/0.44  % (27922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (27922)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (27922)Memory used [KB]: 10618
% 0.22/0.44  % (27922)Time elapsed: 0.005 s
% 0.22/0.44  % (27922)------------------------------
% 0.22/0.44  % (27922)------------------------------
% 0.22/0.44  % (27906)Success in time 0.075 s
%------------------------------------------------------------------------------
