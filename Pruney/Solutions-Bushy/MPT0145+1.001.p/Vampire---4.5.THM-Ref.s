%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0145+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   35 (  53 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :   45 (  66 expanded)
%              Number of equality atoms :   31 (  49 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f109,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f41,f108])).

fof(f108,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | spl7_2 ),
    inference(trivial_inequality_removal,[],[f106])).

fof(f106,plain,
    ( k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k2_tarski(sK4,sK5),k2_enumset1(sK0,sK1,sK2,sK3))) != k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k2_tarski(sK4,sK5),k2_enumset1(sK0,sK1,sK2,sK3)))
    | spl7_2 ),
    inference(forward_demodulation,[],[f92,f12])).

fof(f12,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f92,plain,
    ( k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k2_tarski(sK4,sK5),k2_enumset1(sK0,sK1,sK2,sK3))) != k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)))
    | spl7_2 ),
    inference(superposition,[],[f40,f22])).

fof(f22,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f14,f12])).

fof(f14,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f40,plain,
    ( k2_xboole_0(k2_tarski(sK4,sK5),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK0,sK1,sK2,sK3))) != k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k2_tarski(sK4,sK5),k2_enumset1(sK0,sK1,sK2,sK3)))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl7_2
  <=> k2_xboole_0(k2_tarski(sK4,sK5),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK0,sK1,sK2,sK3))) = k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k2_tarski(sK4,sK5),k2_enumset1(sK0,sK1,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f41,plain,
    ( ~ spl7_2
    | spl7_1 ),
    inference(avatar_split_clause,[],[f36,f32,f38])).

fof(f32,plain,
    ( spl7_1
  <=> k2_xboole_0(k2_tarski(sK4,sK5),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK0,sK1,sK2,sK3))) = k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k1_tarski(sK6),k2_tarski(sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f36,plain,
    ( k2_xboole_0(k2_tarski(sK4,sK5),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK0,sK1,sK2,sK3))) != k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k2_tarski(sK4,sK5),k2_enumset1(sK0,sK1,sK2,sK3)))
    | spl7_1 ),
    inference(forward_demodulation,[],[f34,f22])).

fof(f34,plain,
    ( k2_xboole_0(k2_tarski(sK4,sK5),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK0,sK1,sK2,sK3))) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k1_tarski(sK6),k2_tarski(sK4,sK5)))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f35,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f28,f32])).

fof(f28,plain,(
    k2_xboole_0(k2_tarski(sK4,sK5),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK0,sK1,sK2,sK3))) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k1_tarski(sK6),k2_tarski(sK4,sK5))) ),
    inference(forward_demodulation,[],[f27,f12])).

fof(f27,plain,(
    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k2_tarski(sK4,sK5),k1_tarski(sK6))) != k2_xboole_0(k2_tarski(sK4,sK5),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK0,sK1,sK2,sK3))) ),
    inference(forward_demodulation,[],[f26,f12])).

fof(f26,plain,(
    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k2_tarski(sK4,sK5),k1_tarski(sK6))) != k2_xboole_0(k2_tarski(sK4,sK5),k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_tarski(sK6))) ),
    inference(backward_demodulation,[],[f18,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[],[f14,f12])).

fof(f18,plain,(
    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k2_tarski(sK4,sK5),k1_tarski(sK6))) != k2_xboole_0(k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)),k1_tarski(sK6)) ),
    inference(definition_unfolding,[],[f11,f17,f15])).

fof(f15,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

fof(f17,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X6))) ),
    inference(definition_unfolding,[],[f16,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f16,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).

fof(f11,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

%------------------------------------------------------------------------------
