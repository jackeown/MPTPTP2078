%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0139+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  42 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  55 expanded)
%              Number of equality atoms :   25 (  38 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f39,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f22,f33,f38])).

fof(f38,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f34])).

fof(f34,plain,
    ( $false
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f12,f32])).

fof(f32,plain,
    ( k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_xboole_0(k2_tarski(sK3,sK4),k1_tarski(sK5))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_tarski(sK3,sK4),k1_tarski(sK5))))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl6_2
  <=> k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_xboole_0(k2_tarski(sK3,sK4),k1_tarski(sK5))) = k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_tarski(sK3,sK4),k1_tarski(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f12,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f33,plain,
    ( ~ spl6_2
    | spl6_1 ),
    inference(avatar_split_clause,[],[f28,f19,f30])).

fof(f19,plain,
    ( spl6_1
  <=> k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_xboole_0(k2_tarski(sK3,sK4),k1_tarski(sK5))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(sK3,sK4)),k1_tarski(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f28,plain,
    ( k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_xboole_0(k2_tarski(sK3,sK4),k1_tarski(sK5))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_tarski(sK3,sK4),k1_tarski(sK5))))
    | spl6_1 ),
    inference(forward_demodulation,[],[f27,f12])).

fof(f27,plain,
    ( k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_xboole_0(k2_tarski(sK3,sK4),k1_tarski(sK5))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k2_tarski(sK3,sK4)),k1_tarski(sK5)))
    | spl6_1 ),
    inference(forward_demodulation,[],[f26,f12])).

fof(f26,plain,
    ( k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_xboole_0(k2_tarski(sK3,sK4),k1_tarski(sK5))) != k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK2),k2_tarski(sK3,sK4))),k1_tarski(sK5))
    | spl6_1 ),
    inference(forward_demodulation,[],[f21,f12])).

fof(f21,plain,
    ( k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_xboole_0(k2_tarski(sK3,sK4),k1_tarski(sK5))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(sK3,sK4)),k1_tarski(sK5))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f22,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f17,f19])).

fof(f17,plain,(
    k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_xboole_0(k2_tarski(sK3,sK4),k1_tarski(sK5))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(sK3,sK4)),k1_tarski(sK5)) ),
    inference(definition_unfolding,[],[f10,f16,f15])).

fof(f15,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)),k2_tarski(X3,X4)) ),
    inference(definition_unfolding,[],[f13,f11])).

fof(f11,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f13,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

fof(f16,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)),k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X5))) ),
    inference(definition_unfolding,[],[f14,f11,f11])).

fof(f14,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

fof(f10,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))
   => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

%------------------------------------------------------------------------------
