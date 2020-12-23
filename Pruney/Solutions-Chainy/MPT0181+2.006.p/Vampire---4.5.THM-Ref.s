%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 200 expanded)
%              Number of leaves         :   10 (  71 expanded)
%              Depth                    :   12
%              Number of atoms          :   42 ( 205 expanded)
%              Number of equality atoms :   35 ( 197 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f320,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f319])).

fof(f319,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f30,f251])).

fof(f251,plain,(
    ! [X17,X15,X16] : k3_enumset1(X17,X17,X17,X15,X16) = k3_enumset1(X17,X17,X17,X16,X15) ),
    inference(superposition,[],[f67,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k3_enumset1(X2,X2,X2,X0,X1) = k2_xboole_0(k3_enumset1(X0,X0,X0,X1,X1),k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(superposition,[],[f32,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X0,X0,X0,X1,X1) ),
    inference(superposition,[],[f26,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(definition_unfolding,[],[f18,f21,f23,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f16,f21])).

fof(f16,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f14,f22])).

fof(f14,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f21,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f17,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f17,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f18,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(definition_unfolding,[],[f19,f21,f22,f23])).

fof(f19,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f32,plain,(
    ! [X4,X5,X3] : k2_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_enumset1(X3,X3,X3,X3,X3)) = k3_enumset1(X3,X3,X3,X4,X5) ),
    inference(superposition,[],[f25,f15])).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f67,plain,(
    ! [X10,X11,X9] : k3_enumset1(X11,X11,X11,X9,X10) = k2_xboole_0(k3_enumset1(X10,X10,X10,X9,X9),k3_enumset1(X11,X11,X11,X11,X11)) ),
    inference(superposition,[],[f32,f46])).

fof(f46,plain,(
    ! [X6,X7,X5] : k3_enumset1(X5,X5,X5,X6,X7) = k3_enumset1(X7,X7,X7,X5,X6) ),
    inference(superposition,[],[f32,f26])).

fof(f30,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK2,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl3_1
  <=> k3_enumset1(sK0,sK0,sK0,sK1,sK2) = k3_enumset1(sK0,sK0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f31,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f24,f28])).

fof(f24,plain,(
    k3_enumset1(sK0,sK0,sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK2,sK1) ),
    inference(definition_unfolding,[],[f13,f21,f21])).

fof(f13,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1)
   => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:39:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (19415)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.45  % (19415)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f320,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f31,f319])).
% 0.21/0.45  fof(f319,plain,(
% 0.21/0.45    spl3_1),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f264])).
% 0.21/0.45  fof(f264,plain,(
% 0.21/0.45    $false | spl3_1),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f30,f251])).
% 0.21/0.45  fof(f251,plain,(
% 0.21/0.45    ( ! [X17,X15,X16] : (k3_enumset1(X17,X17,X17,X15,X16) = k3_enumset1(X17,X17,X17,X16,X15)) )),
% 0.21/0.45    inference(superposition,[],[f67,f44])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k3_enumset1(X2,X2,X2,X0,X1) = k2_xboole_0(k3_enumset1(X0,X0,X0,X1,X1),k3_enumset1(X2,X2,X2,X2,X2))) )),
% 0.21/0.45    inference(superposition,[],[f32,f36])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X0,X0,X0,X1,X1)) )),
% 0.21/0.45    inference(superposition,[],[f26,f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f18,f21,f23,f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f16,f21])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f14,f22])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f17,f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f19,f21,f22,f23])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X4,X5,X3] : (k2_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_enumset1(X3,X3,X3,X3,X3)) = k3_enumset1(X3,X3,X3,X4,X5)) )),
% 0.21/0.45    inference(superposition,[],[f25,f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    ( ! [X10,X11,X9] : (k3_enumset1(X11,X11,X11,X9,X10) = k2_xboole_0(k3_enumset1(X10,X10,X10,X9,X9),k3_enumset1(X11,X11,X11,X11,X11))) )),
% 0.21/0.45    inference(superposition,[],[f32,f46])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ( ! [X6,X7,X5] : (k3_enumset1(X5,X5,X5,X6,X7) = k3_enumset1(X7,X7,X7,X5,X6)) )),
% 0.21/0.45    inference(superposition,[],[f32,f26])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    k3_enumset1(sK0,sK0,sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK2,sK1) | spl3_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    spl3_1 <=> k3_enumset1(sK0,sK0,sK0,sK1,sK2) = k3_enumset1(sK0,sK0,sK0,sK2,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ~spl3_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f24,f28])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    k3_enumset1(sK0,sK0,sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK2,sK1)),
% 0.21/0.45    inference(definition_unfolding,[],[f13,f21,f21])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1) => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1)),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1)),
% 0.21/0.45    inference(ennf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 0.21/0.45    inference(negated_conjecture,[],[f8])).
% 0.21/0.45  fof(f8,conjecture,(
% 0.21/0.45    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (19415)------------------------------
% 0.21/0.45  % (19415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (19415)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (19415)Memory used [KB]: 10746
% 0.21/0.45  % (19415)Time elapsed: 0.049 s
% 0.21/0.45  % (19415)------------------------------
% 0.21/0.45  % (19415)------------------------------
% 0.21/0.46  % (19395)Success in time 0.098 s
%------------------------------------------------------------------------------
