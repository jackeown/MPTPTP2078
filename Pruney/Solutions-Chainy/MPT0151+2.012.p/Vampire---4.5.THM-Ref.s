%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  50 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :   12
%              Number of atoms          :   50 (  72 expanded)
%              Number of equality atoms :   30 (  46 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f39,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f32,f38])).

fof(f38,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f37])).

fof(f37,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(trivial_inequality_removal,[],[f36])).

fof(f36,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7))))
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f35,f31])).

fof(f31,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl8_2
  <=> ! [X1,X3,X5,X0,X2,X4] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f35,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7))))
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f21,f34])).

fof(f34,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),X6)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),X6))
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f33,f24])).

fof(f24,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl8_1
  <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f33,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),X6)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)),X6)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(superposition,[],[f24,f31])).

fof(f21,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7)))) ),
    inference(forward_demodulation,[],[f20,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f20,plain,(
    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))) ),
    inference(backward_demodulation,[],[f18,f13])).

fof(f18,plain,(
    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5)),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))) ),
    inference(definition_unfolding,[],[f11,f17,f14,f12])).

fof(f12,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f14,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(f17,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k3_enumset1(X3,X4,X5,X6,X7))) ),
    inference(definition_unfolding,[],[f16,f12,f14])).

fof(f16,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).

fof(f11,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

fof(f32,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f19,f30])).

fof(f19,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(definition_unfolding,[],[f15,f14])).

fof(f15,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(f25,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f13,f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:58:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (18508)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (18500)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (18508)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f25,f32,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ~spl8_1 | ~spl8_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    $false | (~spl8_1 | ~spl8_2)),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7)))) | (~spl8_1 | ~spl8_2)),
% 0.21/0.47    inference(forward_demodulation,[],[f35,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) ) | ~spl8_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    spl8_2 <=> ! [X1,X3,X5,X0,X2,X4] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7)))) | (~spl8_1 | ~spl8_2)),
% 0.21/0.47    inference(backward_demodulation,[],[f21,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),X6)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),X6))) ) | (~spl8_1 | ~spl8_2)),
% 0.21/0.47    inference(forward_demodulation,[],[f33,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl8_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    spl8_1 <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),X6)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)),X6)) ) | (~spl8_1 | ~spl8_2)),
% 0.21/0.47    inference(superposition,[],[f24,f31])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7))))),
% 0.21/0.47    inference(forward_demodulation,[],[f20,f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))),
% 0.21/0.47    inference(backward_demodulation,[],[f18,f13])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5)),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))),
% 0.21/0.47    inference(definition_unfolding,[],[f11,f17,f14,f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k3_enumset1(X3,X4,X5,X6,X7)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f16,f12,f14])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7))),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f8,f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.21/0.47    inference(negated_conjecture,[],[f6])).
% 0.21/0.47  fof(f6,conjecture,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    spl8_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f19,f30])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f15,f14])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    spl8_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f13,f23])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (18508)------------------------------
% 0.21/0.47  % (18508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (18508)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (18508)Memory used [KB]: 6140
% 0.21/0.47  % (18508)Time elapsed: 0.059 s
% 0.21/0.47  % (18508)------------------------------
% 0.21/0.47  % (18508)------------------------------
% 0.21/0.48  % (18512)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (18512)Refutation not found, incomplete strategy% (18512)------------------------------
% 0.21/0.48  % (18512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (18512)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (18512)Memory used [KB]: 10618
% 0.21/0.48  % (18512)Time elapsed: 0.056 s
% 0.21/0.48  % (18512)------------------------------
% 0.21/0.48  % (18512)------------------------------
% 0.21/0.48  % (18498)Success in time 0.123 s
%------------------------------------------------------------------------------
