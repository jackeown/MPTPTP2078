%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   30 (  80 expanded)
%              Number of leaves         :    8 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   34 (  85 expanded)
%              Number of equality atoms :   27 (  77 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f44,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f43])).

fof(f43,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f37])).

fof(f37,plain,
    ( $false
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f25,f33])).

fof(f33,plain,(
    ! [X8,X7,X9] : k1_enumset1(X7,X8,X9) = k2_xboole_0(k1_enumset1(X7,X7,X7),k1_enumset1(X7,X8,X9)) ),
    inference(forward_demodulation,[],[f28,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X1,X1,X2)) ),
    inference(superposition,[],[f21,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)) ),
    inference(definition_unfolding,[],[f14,f17,f13])).

fof(f13,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f17,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f12,f13])).

fof(f12,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f14,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) ),
    inference(definition_unfolding,[],[f16,f18,f13,f13])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) ),
    inference(definition_unfolding,[],[f15,f17])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f28,plain,(
    ! [X8,X7,X9] : k2_xboole_0(k1_enumset1(X7,X7,X7),k1_enumset1(X7,X8,X9)) = k2_xboole_0(k1_enumset1(X7,X7,X8),k1_enumset1(X8,X8,X9)) ),
    inference(superposition,[],[f21,f21])).

fof(f25,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl3_1
  <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f26,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f20,f23])).

fof(f20,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2)) ),
    inference(definition_unfolding,[],[f11,f18])).

fof(f11,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:46:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (6645)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.45  % (6645)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f26,f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    spl3_1),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    $false | spl3_1),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f25,f33])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X8,X7,X9] : (k1_enumset1(X7,X8,X9) = k2_xboole_0(k1_enumset1(X7,X7,X7),k1_enumset1(X7,X8,X9))) )),
% 0.21/0.45    inference(forward_demodulation,[],[f28,f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X1,X1,X2))) )),
% 0.21/0.45    inference(superposition,[],[f21,f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f14,f17,f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f12,f13])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f16,f18,f13,f13])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f15,f17])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X8,X7,X9] : (k2_xboole_0(k1_enumset1(X7,X7,X7),k1_enumset1(X7,X8,X9)) = k2_xboole_0(k1_enumset1(X7,X7,X8),k1_enumset1(X8,X8,X9))) )),
% 0.21/0.45    inference(superposition,[],[f21,f21])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2)) | spl3_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    spl3_1 <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ~spl3_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f20,f23])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2))),
% 0.21/0.45    inference(definition_unfolding,[],[f11,f18])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f8,plain,(
% 0.21/0.45    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.45    inference(negated_conjecture,[],[f6])).
% 0.21/0.45  fof(f6,conjecture,(
% 0.21/0.45    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (6645)------------------------------
% 0.21/0.45  % (6645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (6645)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (6645)Memory used [KB]: 10618
% 0.21/0.45  % (6645)Time elapsed: 0.031 s
% 0.21/0.45  % (6645)------------------------------
% 0.21/0.45  % (6645)------------------------------
% 0.21/0.45  % (6627)Success in time 0.082 s
%------------------------------------------------------------------------------
