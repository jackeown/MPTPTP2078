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
% DateTime   : Thu Dec  3 12:34:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   24 (  38 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :   28 (  43 expanded)
%              Number of equality atoms :   21 (  35 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f28])).

fof(f28,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f24])).

fof(f24,plain,
    ( $false
    | spl1_1 ),
    inference(unit_resulting_resolution,[],[f22,f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)) ),
    inference(definition_unfolding,[],[f13,f16])).

fof(f16,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_enumset1(X7,X7,X7,X7)) ),
    inference(definition_unfolding,[],[f14,f15])).

fof(f15,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f11,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f11,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(f14,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_enumset1)).

fof(f22,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl1_1
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f23,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f18,f20])).

fof(f18,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(definition_unfolding,[],[f10,f15,f16])).

fof(f10,plain,(
    k1_tarski(sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k1_tarski(sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f8])).

fof(f8,plain,
    ( ? [X0] : k1_tarski(X0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
   => k1_tarski(sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] : k1_tarski(X0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:28:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.44  % (7652)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.44  % (7652)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f23,f28])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    spl1_1),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f24])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    $false | spl1_1),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f22,f17])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f13,f16])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_enumset1(X7,X7,X7,X7))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f14,f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.44    inference(definition_unfolding,[],[f11,f12])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.44  fof(f11,plain,(
% 0.20/0.44    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_enumset1)).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    k2_enumset1(sK0,sK0,sK0,sK0) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) | spl1_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f20])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    spl1_1 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ~spl1_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f18,f20])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    k2_enumset1(sK0,sK0,sK0,sK0) != k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.20/0.44    inference(definition_unfolding,[],[f10,f15,f16])).
% 0.20/0.44  fof(f10,plain,(
% 0.20/0.44    k1_tarski(sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,plain,(
% 0.20/0.44    k1_tarski(sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f8])).
% 0.20/0.44  fof(f8,plain,(
% 0.20/0.44    ? [X0] : k1_tarski(X0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) => k1_tarski(sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f7,plain,(
% 0.20/0.44    ? [X0] : k1_tarski(X0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),
% 0.20/0.44    inference(ennf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,negated_conjecture,(
% 0.20/0.44    ~! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),
% 0.20/0.44    inference(negated_conjecture,[],[f5])).
% 0.20/0.44  fof(f5,conjecture,(
% 0.20/0.44    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_enumset1)).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (7652)------------------------------
% 0.20/0.44  % (7652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (7652)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (7652)Memory used [KB]: 10618
% 0.20/0.44  % (7652)Time elapsed: 0.063 s
% 0.20/0.44  % (7652)------------------------------
% 0.20/0.44  % (7652)------------------------------
% 0.20/0.44  % (7634)Success in time 0.101 s
%------------------------------------------------------------------------------
