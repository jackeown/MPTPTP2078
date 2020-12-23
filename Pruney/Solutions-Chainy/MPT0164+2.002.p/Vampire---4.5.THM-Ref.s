%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   24 (  31 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   28 (  36 expanded)
%              Number of equality atoms :   21 (  28 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f25])).

fof(f25,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f24])).

fof(f24,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f22,f18])).

fof(f18,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_enumset1(X0,X0,X1,X2)),k2_tarski(X3,X4)) ),
    inference(definition_unfolding,[],[f13,f12,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X0,X0,X1,X2)) ),
    inference(definition_unfolding,[],[f11,f12])).

fof(f11,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

fof(f12,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f13,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_enumset1)).

fof(f22,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK0,sK0,sK1,sK2)),k2_tarski(sK3,sK4))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl5_1
  <=> k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)) = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK0,sK0,sK1,sK2)),k2_tarski(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f23,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f17,f20])).

fof(f17,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK0,sK0,sK1,sK2)),k2_tarski(sK3,sK4)) ),
    inference(definition_unfolding,[],[f10,f12,f16])).

fof(f16,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)),k2_tarski(X5,X6)) ),
    inference(definition_unfolding,[],[f14,f12])).

fof(f14,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

fof(f10,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k5_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k5_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k5_enumset1(X0,X0,X0,X1,X2,X3,X4)
   => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k5_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:09:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.43  % (4613)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.43  % (4613)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f23,f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    spl5_1),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    $false | spl5_1),
% 0.20/0.43    inference(subsumption_resolution,[],[f22,f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_enumset1(X0,X0,X1,X2)),k2_tarski(X3,X4))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f13,f12,f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X0,X0,X1,X2))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f11,f12])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_enumset1)).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK0,sK0,sK1,sK2)),k2_tarski(sK3,sK4)) | spl5_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    spl5_1 <=> k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)) = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK0,sK0,sK1,sK2)),k2_tarski(sK3,sK4))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ~spl5_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f17,f20])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK0,sK0,sK1,sK2)),k2_tarski(sK3,sK4))),
% 0.20/0.43    inference(definition_unfolding,[],[f10,f12,f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)),k2_tarski(X5,X6))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f14,f12])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k5_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.43    inference(cnf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k5_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f7,f8])).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k5_enumset1(X0,X0,X0,X1,X2,X3,X4) => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k5_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f7,plain,(
% 0.20/0.43    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k5_enumset1(X0,X0,X0,X1,X2,X3,X4)),
% 0.20/0.43    inference(ennf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)),
% 0.20/0.43    inference(negated_conjecture,[],[f5])).
% 0.20/0.43  fof(f5,conjecture,(
% 0.20/0.43    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (4613)------------------------------
% 0.20/0.43  % (4613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (4613)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (4613)Memory used [KB]: 10618
% 0.20/0.43  % (4613)Time elapsed: 0.004 s
% 0.20/0.43  % (4613)------------------------------
% 0.20/0.43  % (4613)------------------------------
% 0.20/0.43  % (4597)Success in time 0.074 s
%------------------------------------------------------------------------------
