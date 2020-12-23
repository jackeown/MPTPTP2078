%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0142+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  40 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  51 expanded)
%              Number of equality atoms :   25 (  36 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f43,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f37,f42])).

fof(f42,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f38])).

fof(f38,plain,
    ( $false
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f11,f36])).

fof(f36,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k1_enumset1(sK4,sK5,sK6)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK4,sK5,sK6)))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl7_2
  <=> k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k1_enumset1(sK4,sK5,sK6)) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK4,sK5,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f11,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f37,plain,
    ( ~ spl7_2
    | spl7_1 ),
    inference(avatar_split_clause,[],[f32,f28,f34])).

fof(f28,plain,
    ( spl7_1
  <=> k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k1_enumset1(sK4,sK5,sK6)) = k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK3),k1_enumset1(sK4,sK5,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f32,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k1_enumset1(sK4,sK5,sK6)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK4,sK5,sK6)))
    | spl7_1 ),
    inference(forward_demodulation,[],[f30,f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_tarski(X3),X4)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_enumset1(X1,X2,X3),X4)) ),
    inference(forward_demodulation,[],[f21,f11])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_tarski(X3),X4)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)),X4) ),
    inference(superposition,[],[f11,f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(definition_unfolding,[],[f13,f12])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f30,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k1_enumset1(sK4,sK5,sK6)) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK3),k1_enumset1(sK4,sK5,sK6)))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f31,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f16,f28])).

fof(f16,plain,(
    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k1_enumset1(sK4,sK5,sK6)) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK3),k1_enumset1(sK4,sK5,sK6))) ),
    inference(definition_unfolding,[],[f10,f15,f12])).

fof(f15,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)),k1_enumset1(X4,X5,X6)) ),
    inference(definition_unfolding,[],[f14,f12])).

fof(f14,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).

fof(f10,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

%------------------------------------------------------------------------------
