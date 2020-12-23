%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 142 expanded)
%              Number of leaves         :   12 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :   54 ( 151 expanded)
%              Number of equality atoms :   43 ( 139 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :   14 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f74,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f64])).

fof(f64,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f63])).

fof(f63,plain,
    ( $false
    | spl7_1 ),
    inference(trivial_inequality_removal,[],[f62])).

fof(f62,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl7_1 ),
    inference(backward_demodulation,[],[f53,f61])).

fof(f61,plain,(
    ! [X6,X10,X8,X7,X11,X9] : k5_xboole_0(k1_tarski(X6),k4_xboole_0(k3_enumset1(X7,X8,X9,X10,X11),k1_tarski(X6))) = k5_xboole_0(k1_tarski(X6),k4_xboole_0(k5_xboole_0(k1_tarski(X7),k4_xboole_0(k5_xboole_0(k1_tarski(X8),k4_xboole_0(k5_xboole_0(k1_tarski(X9),k4_xboole_0(k5_xboole_0(k1_tarski(X10),k4_xboole_0(k1_tarski(X11),k1_tarski(X10))),k1_tarski(X9))),k1_tarski(X8))),k1_tarski(X7))),k1_tarski(X6))) ),
    inference(forward_demodulation,[],[f60,f38])).

fof(f38,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(k4_xboole_0(X4,X3),k4_xboole_0(X5,k5_xboole_0(X3,k4_xboole_0(X4,X3))))) = k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),X3)) ),
    inference(superposition,[],[f31,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
    inference(definition_unfolding,[],[f20,f17,f17,f17,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

% (1966)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f20,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f60,plain,(
    ! [X6,X10,X8,X7,X11,X9] : k5_xboole_0(k1_tarski(X6),k4_xboole_0(k3_enumset1(X7,X8,X9,X10,X11),k1_tarski(X6))) = k5_xboole_0(k1_tarski(X6),k4_xboole_0(k5_xboole_0(k1_tarski(X7),k5_xboole_0(k4_xboole_0(k1_tarski(X8),k1_tarski(X7)),k4_xboole_0(k5_xboole_0(k1_tarski(X9),k4_xboole_0(k5_xboole_0(k1_tarski(X10),k4_xboole_0(k1_tarski(X11),k1_tarski(X10))),k1_tarski(X9))),k5_xboole_0(k1_tarski(X7),k4_xboole_0(k1_tarski(X8),k1_tarski(X7)))))),k1_tarski(X6))) ),
    inference(forward_demodulation,[],[f54,f19])).

fof(f54,plain,(
    ! [X6,X10,X8,X7,X11,X9] : k5_xboole_0(k1_tarski(X6),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X7),k4_xboole_0(k1_tarski(X8),k1_tarski(X7))),k4_xboole_0(k5_xboole_0(k1_tarski(X9),k4_xboole_0(k5_xboole_0(k1_tarski(X10),k4_xboole_0(k1_tarski(X11),k1_tarski(X10))),k1_tarski(X9))),k5_xboole_0(k1_tarski(X7),k4_xboole_0(k1_tarski(X8),k1_tarski(X7))))),k1_tarski(X6))) = k5_xboole_0(k1_tarski(X6),k4_xboole_0(k3_enumset1(X7,X8,X9,X10,X11),k1_tarski(X6))) ),
    inference(superposition,[],[f32,f31])).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k1_tarski(X3))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))))) ),
    inference(definition_unfolding,[],[f23,f25,f17,f27,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f18,f17,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f16,f17])).

fof(f16,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f18,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f22,f17])).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

fof(f53,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl7_1 ),
    inference(forward_demodulation,[],[f52,f38])).

fof(f52,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))))),k1_tarski(sK0)))
    | spl7_1 ),
    inference(forward_demodulation,[],[f50,f19])).

fof(f50,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k1_tarski(sK0)))
    | spl7_1 ),
    inference(superposition,[],[f48,f31])).

fof(f48,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0)))))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl7_1
  <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f49,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f30,f46])).

fof(f30,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))))) ),
    inference(definition_unfolding,[],[f15,f29,f17,f27,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f21,f17,f27])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f24,f17,f25])).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

fof(f15,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:34:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (1962)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (1964)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (1974)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.47  % (1960)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (1975)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (1970)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (1965)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (1967)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (1961)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (1972)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (1975)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f49,f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    spl7_1),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    $false | spl7_1),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1))),k1_tarski(sK0))) | spl7_1),
% 0.22/0.49    inference(backward_demodulation,[],[f53,f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ( ! [X6,X10,X8,X7,X11,X9] : (k5_xboole_0(k1_tarski(X6),k4_xboole_0(k3_enumset1(X7,X8,X9,X10,X11),k1_tarski(X6))) = k5_xboole_0(k1_tarski(X6),k4_xboole_0(k5_xboole_0(k1_tarski(X7),k4_xboole_0(k5_xboole_0(k1_tarski(X8),k4_xboole_0(k5_xboole_0(k1_tarski(X9),k4_xboole_0(k5_xboole_0(k1_tarski(X10),k4_xboole_0(k1_tarski(X11),k1_tarski(X10))),k1_tarski(X9))),k1_tarski(X8))),k1_tarski(X7))),k1_tarski(X6)))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f60,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(k4_xboole_0(X4,X3),k4_xboole_0(X5,k5_xboole_0(X3,k4_xboole_0(X4,X3))))) = k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),X3))) )),
% 0.22/0.49    inference(superposition,[],[f31,f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f20,f17,f17,f17,f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  % (1966)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ( ! [X6,X10,X8,X7,X11,X9] : (k5_xboole_0(k1_tarski(X6),k4_xboole_0(k3_enumset1(X7,X8,X9,X10,X11),k1_tarski(X6))) = k5_xboole_0(k1_tarski(X6),k4_xboole_0(k5_xboole_0(k1_tarski(X7),k5_xboole_0(k4_xboole_0(k1_tarski(X8),k1_tarski(X7)),k4_xboole_0(k5_xboole_0(k1_tarski(X9),k4_xboole_0(k5_xboole_0(k1_tarski(X10),k4_xboole_0(k1_tarski(X11),k1_tarski(X10))),k1_tarski(X9))),k5_xboole_0(k1_tarski(X7),k4_xboole_0(k1_tarski(X8),k1_tarski(X7)))))),k1_tarski(X6)))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f54,f19])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X6,X10,X8,X7,X11,X9] : (k5_xboole_0(k1_tarski(X6),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X7),k4_xboole_0(k1_tarski(X8),k1_tarski(X7))),k4_xboole_0(k5_xboole_0(k1_tarski(X9),k4_xboole_0(k5_xboole_0(k1_tarski(X10),k4_xboole_0(k1_tarski(X11),k1_tarski(X10))),k1_tarski(X9))),k5_xboole_0(k1_tarski(X7),k4_xboole_0(k1_tarski(X8),k1_tarski(X7))))),k1_tarski(X6))) = k5_xboole_0(k1_tarski(X6),k4_xboole_0(k3_enumset1(X7,X8,X9,X10,X11),k1_tarski(X6)))) )),
% 0.22/0.49    inference(superposition,[],[f32,f31])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k1_tarski(X3))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0)))))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f23,f25,f17,f27,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f18,f17,f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f16,f17])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0)))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f22,f17])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) | spl7_1),
% 0.22/0.49    inference(forward_demodulation,[],[f52,f38])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))))),k1_tarski(sK0))) | spl7_1),
% 0.22/0.49    inference(forward_demodulation,[],[f50,f19])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k1_tarski(sK0))) | spl7_1),
% 0.22/0.49    inference(superposition,[],[f48,f31])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))))) | spl7_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    spl7_1 <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0)))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ~spl7_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f30,f46])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0)))))),
% 0.22/0.49    inference(definition_unfolding,[],[f15,f29,f17,f27,f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f21,f17,f27])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f24,f17,f25])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6))),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f12,f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.22/0.49    inference(negated_conjecture,[],[f10])).
% 0.22/0.49  fof(f10,conjecture,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (1975)------------------------------
% 0.22/0.49  % (1975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (1975)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (1975)Memory used [KB]: 10746
% 0.22/0.49  % (1975)Time elapsed: 0.016 s
% 0.22/0.49  % (1975)------------------------------
% 0.22/0.49  % (1975)------------------------------
% 0.22/0.49  % (1959)Success in time 0.129 s
%------------------------------------------------------------------------------
