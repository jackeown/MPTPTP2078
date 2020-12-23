%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 350 expanded)
%              Number of leaves         :   12 ( 143 expanded)
%              Depth                    :   13
%              Number of atoms          :   63 ( 368 expanded)
%              Number of equality atoms :   45 ( 345 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f155,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f40,f119,f154])).

fof(f154,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f103,f118])).

fof(f118,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k2_tarski(sK3,sK4),k4_xboole_0(k2_tarski(sK5,sK6),k2_tarski(sK3,sK4))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl7_3
  <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k2_tarski(sK3,sK4),k4_xboole_0(k2_tarski(sK5,sK6),k2_tarski(sK3,sK4))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f103,plain,(
    ! [X12,X10,X8,X7,X13,X11,X9] : k5_xboole_0(k1_tarski(X7),k4_xboole_0(k4_enumset1(X8,X9,X10,X11,X12,X13),k1_tarski(X7))) = k5_xboole_0(k1_tarski(X7),k4_xboole_0(k5_xboole_0(k1_tarski(X8),k4_xboole_0(k5_xboole_0(k1_tarski(X9),k4_xboole_0(k5_xboole_0(k2_tarski(X10,X11),k4_xboole_0(k2_tarski(X12,X13),k2_tarski(X10,X11))),k1_tarski(X9))),k1_tarski(X8))),k1_tarski(X7))) ),
    inference(backward_demodulation,[],[f48,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k2_tarski(X2,X3),k4_xboole_0(X4,k2_tarski(X2,X3))),k1_tarski(X1))),k1_tarski(X0))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(X4,k1_tarski(X3))),k2_tarski(X1,X2))),k1_tarski(X0))) ),
    inference(forward_demodulation,[],[f54,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
    inference(definition_unfolding,[],[f16,f14,f14,f14,f14])).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f16,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X1,X2),k4_xboole_0(k1_tarski(X3),k2_tarski(X1,X2))),k4_xboole_0(X4,k5_xboole_0(k2_tarski(X1,X2),k4_xboole_0(k1_tarski(X3),k2_tarski(X1,X2))))),k1_tarski(X0))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k2_tarski(X2,X3),k4_xboole_0(X4,k2_tarski(X2,X3))),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(forward_demodulation,[],[f53,f25])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X1,X2),k4_xboole_0(k1_tarski(X3),k2_tarski(X1,X2))),k4_xboole_0(X4,k5_xboole_0(k2_tarski(X1,X2),k4_xboole_0(k1_tarski(X3),k2_tarski(X1,X2))))),k1_tarski(X0))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k4_xboole_0(X4,k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))))),k1_tarski(X0))) ),
    inference(forward_demodulation,[],[f52,f25])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X1,X2),k4_xboole_0(k1_tarski(X3),k2_tarski(X1,X2))),k4_xboole_0(X4,k5_xboole_0(k2_tarski(X1,X2),k4_xboole_0(k1_tarski(X3),k2_tarski(X1,X2))))),k1_tarski(X0))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k1_tarski(X0))),k4_xboole_0(X4,k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k1_tarski(X0))))) ),
    inference(superposition,[],[f25,f41])).

fof(f41,plain,(
    ! [X6,X4,X7,X5] : k5_xboole_0(k1_tarski(X4),k4_xboole_0(k5_xboole_0(k2_tarski(X5,X6),k4_xboole_0(k1_tarski(X7),k2_tarski(X5,X6))),k1_tarski(X4))) = k5_xboole_0(k1_tarski(X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k2_tarski(X6,X7),k1_tarski(X5))),k1_tarski(X4))) ),
    inference(superposition,[],[f26,f25])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k1_tarski(X0))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))),k4_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))))) ),
    inference(definition_unfolding,[],[f18,f23,f14,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f15,f14])).

fof(f15,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f17,f14,f22])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f48,plain,(
    ! [X12,X10,X8,X7,X13,X11,X9] : k5_xboole_0(k1_tarski(X7),k4_xboole_0(k4_enumset1(X8,X9,X10,X11,X12,X13),k1_tarski(X7))) = k5_xboole_0(k1_tarski(X7),k4_xboole_0(k5_xboole_0(k1_tarski(X8),k4_xboole_0(k5_xboole_0(k2_tarski(X9,X10),k4_xboole_0(k5_xboole_0(k1_tarski(X11),k4_xboole_0(k2_tarski(X12,X13),k1_tarski(X11))),k2_tarski(X9,X10))),k1_tarski(X8))),k1_tarski(X7))) ),
    inference(forward_demodulation,[],[f45,f25])).

fof(f45,plain,(
    ! [X12,X10,X8,X7,X13,X11,X9] : k5_xboole_0(k1_tarski(X7),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X8),k4_xboole_0(k2_tarski(X9,X10),k1_tarski(X8))),k4_xboole_0(k5_xboole_0(k1_tarski(X11),k4_xboole_0(k2_tarski(X12,X13),k1_tarski(X11))),k5_xboole_0(k1_tarski(X8),k4_xboole_0(k2_tarski(X9,X10),k1_tarski(X8))))),k1_tarski(X7))) = k5_xboole_0(k1_tarski(X7),k4_xboole_0(k4_enumset1(X8,X9,X10,X11,X12,X13),k1_tarski(X7))) ),
    inference(superposition,[],[f27,f25])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k2_tarski(X5,X6),k1_tarski(X4))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k1_tarski(X0))))) ),
    inference(definition_unfolding,[],[f20,f21,f14,f23,f22])).

fof(f21,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f19,f14])).

fof(f19,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

fof(f20,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

fof(f119,plain,
    ( ~ spl7_3
    | spl7_2 ),
    inference(avatar_split_clause,[],[f114,f37,f116])).

fof(f37,plain,
    ( spl7_2
  <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k2_tarski(sK1,sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK4))),k1_tarski(sK3))),k2_tarski(sK1,sK2))),k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f114,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k2_tarski(sK3,sK4),k4_xboole_0(k2_tarski(sK5,sK6),k2_tarski(sK3,sK4))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl7_2 ),
    inference(forward_demodulation,[],[f106,f55])).

fof(f106,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK4))),k2_tarski(sK2,sK3))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl7_2 ),
    inference(superposition,[],[f39,f55])).

fof(f39,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k2_tarski(sK1,sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK4))),k1_tarski(sK3))),k2_tarski(sK1,sK2))),k1_tarski(sK0)))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f40,plain,
    ( ~ spl7_2
    | spl7_1 ),
    inference(avatar_split_clause,[],[f34,f29,f37])).

fof(f29,plain,
    ( spl7_1
  <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f34,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k2_tarski(sK1,sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK4))),k1_tarski(sK3))),k2_tarski(sK1,sK2))),k1_tarski(sK0)))
    | spl7_1 ),
    inference(superposition,[],[f31,f25])).

fof(f31,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0)))))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f32,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f24,f29])).

fof(f24,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))))) ),
    inference(definition_unfolding,[],[f13,f21,f14,f22,f23])).

fof(f13,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:54:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (14529)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.45  % (14536)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.45  % (14529)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f155,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f32,f40,f119,f154])).
% 0.21/0.45  fof(f154,plain,(
% 0.21/0.45    spl7_3),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f150])).
% 0.21/0.45  fof(f150,plain,(
% 0.21/0.45    $false | spl7_3),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f103,f118])).
% 0.21/0.45  fof(f118,plain,(
% 0.21/0.45    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k2_tarski(sK3,sK4),k4_xboole_0(k2_tarski(sK5,sK6),k2_tarski(sK3,sK4))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) | spl7_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f116])).
% 0.21/0.45  fof(f116,plain,(
% 0.21/0.45    spl7_3 <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k2_tarski(sK3,sK4),k4_xboole_0(k2_tarski(sK5,sK6),k2_tarski(sK3,sK4))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.45  fof(f103,plain,(
% 0.21/0.45    ( ! [X12,X10,X8,X7,X13,X11,X9] : (k5_xboole_0(k1_tarski(X7),k4_xboole_0(k4_enumset1(X8,X9,X10,X11,X12,X13),k1_tarski(X7))) = k5_xboole_0(k1_tarski(X7),k4_xboole_0(k5_xboole_0(k1_tarski(X8),k4_xboole_0(k5_xboole_0(k1_tarski(X9),k4_xboole_0(k5_xboole_0(k2_tarski(X10,X11),k4_xboole_0(k2_tarski(X12,X13),k2_tarski(X10,X11))),k1_tarski(X9))),k1_tarski(X8))),k1_tarski(X7)))) )),
% 0.21/0.45    inference(backward_demodulation,[],[f48,f55])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k2_tarski(X2,X3),k4_xboole_0(X4,k2_tarski(X2,X3))),k1_tarski(X1))),k1_tarski(X0))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(X4,k1_tarski(X3))),k2_tarski(X1,X2))),k1_tarski(X0)))) )),
% 0.21/0.45    inference(forward_demodulation,[],[f54,f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f16,f14,f14,f14,f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X1,X2),k4_xboole_0(k1_tarski(X3),k2_tarski(X1,X2))),k4_xboole_0(X4,k5_xboole_0(k2_tarski(X1,X2),k4_xboole_0(k1_tarski(X3),k2_tarski(X1,X2))))),k1_tarski(X0))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k2_tarski(X2,X3),k4_xboole_0(X4,k2_tarski(X2,X3))),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.21/0.45    inference(forward_demodulation,[],[f53,f25])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X1,X2),k4_xboole_0(k1_tarski(X3),k2_tarski(X1,X2))),k4_xboole_0(X4,k5_xboole_0(k2_tarski(X1,X2),k4_xboole_0(k1_tarski(X3),k2_tarski(X1,X2))))),k1_tarski(X0))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k4_xboole_0(X4,k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))))),k1_tarski(X0)))) )),
% 0.21/0.45    inference(forward_demodulation,[],[f52,f25])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k2_tarski(X1,X2),k4_xboole_0(k1_tarski(X3),k2_tarski(X1,X2))),k4_xboole_0(X4,k5_xboole_0(k2_tarski(X1,X2),k4_xboole_0(k1_tarski(X3),k2_tarski(X1,X2))))),k1_tarski(X0))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k1_tarski(X0))),k4_xboole_0(X4,k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k1_tarski(X0)))))) )),
% 0.21/0.45    inference(superposition,[],[f25,f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ( ! [X6,X4,X7,X5] : (k5_xboole_0(k1_tarski(X4),k4_xboole_0(k5_xboole_0(k2_tarski(X5,X6),k4_xboole_0(k1_tarski(X7),k2_tarski(X5,X6))),k1_tarski(X4))) = k5_xboole_0(k1_tarski(X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k2_tarski(X6,X7),k1_tarski(X5))),k1_tarski(X4)))) )),
% 0.21/0.45    inference(superposition,[],[f26,f25])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k1_tarski(X0))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))),k4_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)))))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f18,f23,f14,f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f15,f14])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f17,f14,f22])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ( ! [X12,X10,X8,X7,X13,X11,X9] : (k5_xboole_0(k1_tarski(X7),k4_xboole_0(k4_enumset1(X8,X9,X10,X11,X12,X13),k1_tarski(X7))) = k5_xboole_0(k1_tarski(X7),k4_xboole_0(k5_xboole_0(k1_tarski(X8),k4_xboole_0(k5_xboole_0(k2_tarski(X9,X10),k4_xboole_0(k5_xboole_0(k1_tarski(X11),k4_xboole_0(k2_tarski(X12,X13),k1_tarski(X11))),k2_tarski(X9,X10))),k1_tarski(X8))),k1_tarski(X7)))) )),
% 0.21/0.46    inference(forward_demodulation,[],[f45,f25])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ( ! [X12,X10,X8,X7,X13,X11,X9] : (k5_xboole_0(k1_tarski(X7),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X8),k4_xboole_0(k2_tarski(X9,X10),k1_tarski(X8))),k4_xboole_0(k5_xboole_0(k1_tarski(X11),k4_xboole_0(k2_tarski(X12,X13),k1_tarski(X11))),k5_xboole_0(k1_tarski(X8),k4_xboole_0(k2_tarski(X9,X10),k1_tarski(X8))))),k1_tarski(X7))) = k5_xboole_0(k1_tarski(X7),k4_xboole_0(k4_enumset1(X8,X9,X10,X11,X12,X13),k1_tarski(X7)))) )),
% 0.21/0.46    inference(superposition,[],[f27,f25])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k2_tarski(X5,X6),k1_tarski(X4))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k1_tarski(X0)))))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f20,f21,f14,f23,f22])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0)))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f19,f14])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).
% 0.21/0.46  fof(f119,plain,(
% 0.21/0.46    ~spl7_3 | spl7_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f114,f37,f116])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    spl7_2 <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k2_tarski(sK1,sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK4))),k1_tarski(sK3))),k2_tarski(sK1,sK2))),k1_tarski(sK0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.46  fof(f114,plain,(
% 0.21/0.46    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k2_tarski(sK3,sK4),k4_xboole_0(k2_tarski(sK5,sK6),k2_tarski(sK3,sK4))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) | spl7_2),
% 0.21/0.46    inference(forward_demodulation,[],[f106,f55])).
% 0.21/0.46  fof(f106,plain,(
% 0.21/0.46    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k2_tarski(sK2,sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK4))),k2_tarski(sK2,sK3))),k1_tarski(sK1))),k1_tarski(sK0))) | spl7_2),
% 0.21/0.46    inference(superposition,[],[f39,f55])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k2_tarski(sK1,sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK4))),k1_tarski(sK3))),k2_tarski(sK1,sK2))),k1_tarski(sK0))) | spl7_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f37])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ~spl7_2 | spl7_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f34,f29,f37])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    spl7_1 <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0)))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k2_tarski(sK1,sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK4))),k1_tarski(sK3))),k2_tarski(sK1,sK2))),k1_tarski(sK0))) | spl7_1),
% 0.21/0.46    inference(superposition,[],[f31,f25])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))))) | spl7_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f29])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ~spl7_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f24,f29])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0)))))),
% 0.21/0.46    inference(definition_unfolding,[],[f13,f21,f14,f22,f23])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6))),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f10,f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.21/0.46    inference(negated_conjecture,[],[f8])).
% 0.21/0.46  fof(f8,conjecture,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (14529)------------------------------
% 0.21/0.46  % (14529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (14529)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (14529)Memory used [KB]: 6396
% 0.21/0.46  % (14529)Time elapsed: 0.019 s
% 0.21/0.46  % (14529)------------------------------
% 0.21/0.46  % (14529)------------------------------
% 0.21/0.46  % (14528)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (14518)Success in time 0.103 s
%------------------------------------------------------------------------------
