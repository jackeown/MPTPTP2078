%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :    7 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   26 (  28 expanded)
%              Number of equality atoms :   19 (  20 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f26])).

fof(f26,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f25])).

fof(f25,plain,
    ( $false
    | spl9_1 ),
    inference(subsumption_resolution,[],[f23,f11])).

fof(f11,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f23,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl9_1
  <=> k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f24,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f16,f21])).

fof(f16,plain,(
    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) ),
    inference(definition_unfolding,[],[f10,f15,f13])).

fof(f13,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_enumset1)).

fof(f15,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(definition_unfolding,[],[f14,f12])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f14,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l142_enumset1)).

fof(f10,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_tarski(sK0),k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_tarski(sK0),k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))
   => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_tarski(sK0),k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:02:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (15755)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.43  % (15755)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f24,f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    spl9_1),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    $false | spl9_1),
% 0.21/0.43    inference(subsumption_resolution,[],[f23,f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) | spl9_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    spl9_1 <=> k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ~spl9_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f16,f21])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)))),
% 0.21/0.43    inference(definition_unfolding,[],[f10,f15,f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_enumset1)).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)),k3_enumset1(X4,X5,X6,X7,X8))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f14,f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l142_enumset1)).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_tarski(sK0),k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_tarski(sK0),k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f7,f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_tarski(sK0),k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))),
% 0.21/0.43    inference(negated_conjecture,[],[f5])).
% 0.21/0.43  fof(f5,conjecture,(
% 0.21/0.43    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_enumset1)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (15755)------------------------------
% 0.21/0.43  % (15755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (15755)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (15755)Memory used [KB]: 10618
% 0.21/0.43  % (15755)Time elapsed: 0.005 s
% 0.21/0.43  % (15755)------------------------------
% 0.21/0.43  % (15755)------------------------------
% 0.21/0.43  % (15739)Success in time 0.069 s
%------------------------------------------------------------------------------
