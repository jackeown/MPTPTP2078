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
% DateTime   : Thu Dec  3 12:33:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 (  90 expanded)
%              Number of leaves         :   10 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :   44 (  95 expanded)
%              Number of equality atoms :   37 (  87 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f83])).

fof(f83,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | spl7_1 ),
    inference(subsumption_resolution,[],[f80,f55])).

fof(f55,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(k3_xboole_0(X5,X4),k3_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))),X3))))) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,X3),k5_xboole_0(X5,k3_xboole_0(X5,k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3)))))))) ),
    inference(forward_demodulation,[],[f40,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f40,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X4,k3_xboole_0(X4,X3)),k5_xboole_0(X5,k3_xboole_0(X5,k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))))))) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(k3_xboole_0(X5,X4),k3_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))),X3))))) ),
    inference(superposition,[],[f32,f17])).

fof(f32,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))))) ),
    inference(forward_demodulation,[],[f31,f17])).

fof(f31,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0)))) ),
    inference(forward_demodulation,[],[f26,f17])).

fof(f26,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))) ),
    inference(definition_unfolding,[],[f18,f21,f21,f21,f21])).

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

fof(f18,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f80,plain,
    ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1)),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1)))),k1_tarski(sK0))))))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl7_1
  <=> k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))))) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1)),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1)))),k1_tarski(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f81,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f30,f78])).

fof(f30,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1)),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1)))),k1_tarski(sK0)))))) ),
    inference(forward_demodulation,[],[f29,f17])).

fof(f29,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1)))),k1_tarski(sK0))))) ),
    inference(forward_demodulation,[],[f28,f17])).

fof(f28,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1)))),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))))) ),
    inference(forward_demodulation,[],[f27,f17])).

fof(f27,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1)))),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))))) ),
    inference(backward_demodulation,[],[f25,f17])).

fof(f25,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1)))),k1_tarski(sK0)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) ),
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

fof(f24,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1)))),k1_tarski(X0)))) ),
    inference(definition_unfolding,[],[f20,f21,f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k3_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0)))) ),
    inference(definition_unfolding,[],[f19,f21])).

fof(f19,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(f20,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

fof(f13,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:56:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (2818)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.45  % (2805)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.45  % (2807)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.45  % (2803)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.45  % (2818)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f84,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f81,f83])).
% 0.20/0.45  fof(f83,plain,(
% 0.20/0.45    spl7_1),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f82])).
% 0.20/0.45  fof(f82,plain,(
% 0.20/0.45    $false | spl7_1),
% 0.20/0.45    inference(subsumption_resolution,[],[f80,f55])).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(k3_xboole_0(X5,X4),k3_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))),X3))))) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,X3),k5_xboole_0(X5,k3_xboole_0(X5,k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))))))))) )),
% 0.20/0.46    inference(forward_demodulation,[],[f40,f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X4,k3_xboole_0(X4,X3)),k5_xboole_0(X5,k3_xboole_0(X5,k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))))))) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(k3_xboole_0(X5,X4),k3_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))),X3)))))) )),
% 0.20/0.46    inference(superposition,[],[f32,f17])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0)))))) )),
% 0.20/0.46    inference(forward_demodulation,[],[f31,f17])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))))) )),
% 0.20/0.46    inference(forward_demodulation,[],[f26,f17])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0)))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f18,f21,f21,f21,f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f16,f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1)),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1)))),k1_tarski(sK0)))))) | spl7_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f78])).
% 0.20/0.46  fof(f78,plain,(
% 0.20/0.46    spl7_1 <=> k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))))) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1)),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1)))),k1_tarski(sK0))))))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.46  fof(f81,plain,(
% 0.20/0.46    ~spl7_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f30,f78])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1)),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1)))),k1_tarski(sK0))))))),
% 0.20/0.46    inference(forward_demodulation,[],[f29,f17])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1)))),k1_tarski(sK0)))))),
% 0.20/0.46    inference(forward_demodulation,[],[f28,f17])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1)))),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))))))),
% 0.20/0.46    inference(forward_demodulation,[],[f27,f17])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1)))),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))))),
% 0.20/0.46    inference(backward_demodulation,[],[f25,f17])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1)))),k1_tarski(sK0)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k3_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))))),
% 0.20/0.46    inference(definition_unfolding,[],[f13,f24,f21,f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0))))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f14,f21])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1)))),k1_tarski(X0))))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f20,f21,f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k3_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f19,f21])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6))),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f10,f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 0.20/0.46    inference(ennf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 0.20/0.46    inference(negated_conjecture,[],[f8])).
% 0.20/0.46  fof(f8,conjecture,(
% 0.20/0.46    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (2818)------------------------------
% 0.20/0.46  % (2818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (2818)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (2818)Memory used [KB]: 10746
% 0.20/0.46  % (2818)Time elapsed: 0.008 s
% 0.20/0.46  % (2818)------------------------------
% 0.20/0.46  % (2818)------------------------------
% 0.20/0.46  % (2802)Success in time 0.109 s
%------------------------------------------------------------------------------
