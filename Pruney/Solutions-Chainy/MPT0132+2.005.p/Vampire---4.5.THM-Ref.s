%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  94 expanded)
%              Number of leaves         :   11 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :   55 ( 110 expanded)
%              Number of equality atoms :   39 (  90 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f43,f65])).

fof(f65,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f64])).

fof(f64,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f30,f63])).

fof(f63,plain,
    ( ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(k3_xboole_0(X5,X4),k3_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))),X3))))) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,X3),k5_xboole_0(X5,k3_xboole_0(X5,k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))))))))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f48,f35])).

% (16930)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f35,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl5_1
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f48,plain,
    ( ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X4,k3_xboole_0(X4,X3)),k5_xboole_0(X5,k3_xboole_0(X5,k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))))))) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(k3_xboole_0(X5,X4),k3_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))),X3)))))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(superposition,[],[f42,f35])).

fof(f42,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0)))))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl5_2
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f30,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k1_tarski(sK0)))))) ),
    inference(forward_demodulation,[],[f29,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f29,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k1_tarski(sK0))))) ),
    inference(forward_demodulation,[],[f28,f17])).

fof(f28,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))))) ),
    inference(forward_demodulation,[],[f27,f17])).

fof(f27,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))))) ),
    inference(backward_demodulation,[],[f25,f17])).

fof(f25,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k1_tarski(sK0)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) ),
    inference(definition_unfolding,[],[f13,f24,f21,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))) ),
    inference(definition_unfolding,[],[f14,f21])).

fof(f14,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f16,f15])).

fof(f15,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))),k1_tarski(X0)))) ),
    inference(definition_unfolding,[],[f20,f21,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)))) ),
    inference(definition_unfolding,[],[f19,f21])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f13,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_tarski(sK0,sK1),k1_enumset1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_tarski(sK0,sK1),k1_enumset1(sK2,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))
   => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_tarski(sK0,sK1),k1_enumset1(sK2,sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

fof(f43,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f32,f41])).

fof(f32,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))))) ),
    inference(forward_demodulation,[],[f31,f17])).

fof(f31,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0)))) ),
    inference(forward_demodulation,[],[f26,f17])).

fof(f26,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))) ),
    inference(definition_unfolding,[],[f18,f21,f21,f21,f21])).

fof(f18,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f36,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f17,f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:25:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (16923)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (16934)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.47  % (16925)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (16926)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (16931)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (16919)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (16932)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (16925)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f36,f43,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ~spl5_1 | ~spl5_2),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    $false | (~spl5_1 | ~spl5_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f30,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(k3_xboole_0(X5,X4),k3_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))),X3))))) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,X3),k5_xboole_0(X5,k3_xboole_0(X5,k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))))))))) ) | (~spl5_1 | ~spl5_2)),
% 0.21/0.48    inference(forward_demodulation,[],[f48,f35])).
% 0.21/0.48  % (16930)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl5_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    spl5_1 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X4,k3_xboole_0(X4,X3)),k5_xboole_0(X5,k3_xboole_0(X5,k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))))))) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(k3_xboole_0(X5,X4),k3_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))),X3)))))) ) | (~spl5_1 | ~spl5_2)),
% 0.21/0.48    inference(superposition,[],[f42,f35])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0)))))) ) | ~spl5_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    spl5_2 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0)))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k1_tarski(sK0))))))),
% 0.21/0.48    inference(forward_demodulation,[],[f29,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k1_tarski(sK0)))))),
% 0.21/0.48    inference(forward_demodulation,[],[f28,f17])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))))))),
% 0.21/0.48    inference(forward_demodulation,[],[f27,f17])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))))),
% 0.21/0.48    inference(backward_demodulation,[],[f25,f17])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k1_tarski(sK0)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))))),
% 0.21/0.48    inference(definition_unfolding,[],[f13,f24,f21,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0))))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f14,f21])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f16,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))),k1_tarski(X0))))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f20,f21,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0))))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f19,f21])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_tarski(sK0,sK1),k1_enumset1(sK2,sK3,sK4))),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_tarski(sK0,sK1),k1_enumset1(sK2,sK3,sK4))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_tarski(sK0,sK1),k1_enumset1(sK2,sK3,sK4))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.21/0.48    inference(negated_conjecture,[],[f8])).
% 0.21/0.48  fof(f8,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    spl5_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f41])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0)))))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f31,f17])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f26,f17])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f18,f21,f21,f21,f21])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f17,f34])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (16925)------------------------------
% 0.21/0.48  % (16925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (16925)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (16925)Memory used [KB]: 6268
% 0.21/0.48  % (16925)Time elapsed: 0.059 s
% 0.21/0.48  % (16925)------------------------------
% 0.21/0.48  % (16925)------------------------------
% 0.21/0.48  % (16921)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (16917)Success in time 0.115 s
%------------------------------------------------------------------------------
