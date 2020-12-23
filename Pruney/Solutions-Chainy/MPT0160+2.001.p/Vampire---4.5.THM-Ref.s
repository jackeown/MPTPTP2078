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
% DateTime   : Thu Dec  3 12:33:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   22 (  30 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    8
%              Number of atoms          :   26 (  35 expanded)
%              Number of equality atoms :   19 (  27 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f26])).

fof(f26,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f22])).

fof(f22,plain,
    ( $false
    | spl1_1 ),
    inference(unit_resulting_resolution,[],[f20,f14])).

fof(f14,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(definition_unfolding,[],[f10,f11])).

fof(f11,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f10,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,
    ( k1_tarski(sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl1_1
  <=> k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f21,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f16,f18])).

fof(f16,plain,(
    k1_tarski(sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f15,f14])).

fof(f15,plain,(
    k1_tarski(sK0) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0))) ),
    inference(definition_unfolding,[],[f9,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) ),
    inference(definition_unfolding,[],[f12,f11])).

fof(f12,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f9,plain,(
    k1_tarski(sK0) != k1_enumset1(sK0,sK0,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k1_tarski(sK0) != k1_enumset1(sK0,sK0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f7])).

fof(f7,plain,
    ( ? [X0] : k1_tarski(X0) != k1_enumset1(X0,X0,X0)
   => k1_tarski(sK0) != k1_enumset1(sK0,sK0,sK0) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] : k1_tarski(X0) != k1_enumset1(X0,X0,X0) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:37:17 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (18781)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.45  % (18781)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f21,f26])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    spl1_1),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f22])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    $false | spl1_1),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f20,f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ( ! [X0] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 0.22/0.45    inference(definition_unfolding,[],[f10,f11])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    k1_tarski(sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) | spl1_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    spl1_1 <=> k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ~spl1_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f16,f18])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    k1_tarski(sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 0.22/0.45    inference(forward_demodulation,[],[f15,f14])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    k1_tarski(sK0) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))),
% 0.22/0.45    inference(definition_unfolding,[],[f9,f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2)))) )),
% 0.22/0.45    inference(definition_unfolding,[],[f12,f11])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.22/0.45  fof(f9,plain,(
% 0.22/0.45    k1_tarski(sK0) != k1_enumset1(sK0,sK0,sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f8])).
% 0.22/0.45  fof(f8,plain,(
% 0.22/0.45    k1_tarski(sK0) != k1_enumset1(sK0,sK0,sK0)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f7])).
% 0.22/0.45  fof(f7,plain,(
% 0.22/0.45    ? [X0] : k1_tarski(X0) != k1_enumset1(X0,X0,X0) => k1_tarski(sK0) != k1_enumset1(sK0,sK0,sK0)),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f6,plain,(
% 0.22/0.45    ? [X0] : k1_tarski(X0) != k1_enumset1(X0,X0,X0)),
% 0.22/0.45    inference(ennf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,negated_conjecture,(
% 0.22/0.45    ~! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0)),
% 0.22/0.45    inference(negated_conjecture,[],[f4])).
% 0.22/0.45  fof(f4,conjecture,(
% 0.22/0.45    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (18781)------------------------------
% 0.22/0.45  % (18781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (18781)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (18781)Memory used [KB]: 10490
% 0.22/0.45  % (18781)Time elapsed: 0.002 s
% 0.22/0.45  % (18781)------------------------------
% 0.22/0.45  % (18781)------------------------------
% 0.22/0.45  % (18763)Success in time 0.083 s
%------------------------------------------------------------------------------
