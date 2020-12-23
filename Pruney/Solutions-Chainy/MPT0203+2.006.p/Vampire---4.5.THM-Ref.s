%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   28 (  38 expanded)
%              Number of leaves         :    8 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :   32 (  43 expanded)
%              Number of equality atoms :   25 (  35 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f46,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f42])).

fof(f42,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f36])).

fof(f36,plain,
    ( $false
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f34,f25])).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X6),k2_xboole_0(k3_enumset1(X7,X8,X0,X1,X2),k1_enumset1(X3,X4,X5))) = k2_xboole_0(k1_enumset1(X6,X7,X8),k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) ),
    inference(superposition,[],[f24,f19])).

fof(f19,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(definition_unfolding,[],[f14,f13])).

fof(f13,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(f14,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_enumset1)).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),X6)) ),
    inference(forward_demodulation,[],[f23,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f23,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)),X6) ),
    inference(superposition,[],[f12,f19])).

fof(f34,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8))) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl9_1
  <=> k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8))) = k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f35,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f18,f32])).

fof(f18,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8))) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) ),
    inference(definition_unfolding,[],[f11,f17,f13])).

fof(f17,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))) ),
    inference(definition_unfolding,[],[f16,f15])).

fof(f15,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).

fof(f16,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_enumset1)).

fof(f11,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))
   => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (2417)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.42  % (2417)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f35,f42])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    spl9_1),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f36])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    $false | spl9_1),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f34,f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X6),k2_xboole_0(k3_enumset1(X7,X8,X0,X1,X2),k1_enumset1(X3,X4,X5))) = k2_xboole_0(k1_enumset1(X6,X7,X8),k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)))) )),
% 0.21/0.42    inference(superposition,[],[f24,f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.21/0.42    inference(definition_unfolding,[],[f14,f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_enumset1)).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),X6))) )),
% 0.21/0.42    inference(forward_demodulation,[],[f23,f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)),X6)) )),
% 0.21/0.42    inference(superposition,[],[f12,f19])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8))) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) | spl9_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f32])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    spl9_1 <=> k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8))) = k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    ~spl9_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f18,f32])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8))) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)))),
% 0.21/0.42    inference(definition_unfolding,[],[f11,f17,f13])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)))) )),
% 0.21/0.42    inference(definition_unfolding,[],[f16,f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_enumset1)).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f8,f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))),
% 0.21/0.42    inference(negated_conjecture,[],[f6])).
% 0.21/0.42  fof(f6,conjecture,(
% 0.21/0.42    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_enumset1)).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (2417)------------------------------
% 0.21/0.42  % (2417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (2417)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (2417)Memory used [KB]: 10618
% 0.21/0.42  % (2417)Time elapsed: 0.005 s
% 0.21/0.42  % (2417)------------------------------
% 0.21/0.42  % (2417)------------------------------
% 0.21/0.43  % (2399)Success in time 0.071 s
%------------------------------------------------------------------------------
