%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 162 expanded)
%              Number of leaves         :   12 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :   59 ( 171 expanded)
%              Number of equality atoms :   48 ( 159 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f78,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f77])).

% (32039)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
fof(f77,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f76])).

fof(f76,plain,
    ( $false
    | spl7_1 ),
    inference(trivial_inequality_removal,[],[f75])).

fof(f75,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl7_1 ),
    inference(forward_demodulation,[],[f74,f58])).

fof(f58,plain,(
    ! [X6,X8,X7,X5,X9] : k5_xboole_0(k1_tarski(X9),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k1_tarski(X9))) = k5_xboole_0(k1_tarski(X5),k4_xboole_0(k2_enumset1(X6,X7,X8,X9),k1_tarski(X5))) ),
    inference(superposition,[],[f33,f30])).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f16,f18,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0))) = k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3))) ),
    inference(definition_unfolding,[],[f22,f26,f18])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f21,f18])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f74,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k1_tarski(sK6))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl7_1 ),
    inference(forward_demodulation,[],[f73,f30])).

fof(f73,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k4_xboole_0(k1_tarski(sK6),k2_enumset1(sK2,sK3,sK4,sK5))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl7_1 ),
    inference(forward_demodulation,[],[f72,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(X5,k1_tarski(X4))),k2_enumset1(X0,X1,X2,X3))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(X5,k2_enumset1(X1,X2,X3,X4))),k1_tarski(X0))) ),
    inference(forward_demodulation,[],[f65,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X2,X0),X1)) ),
    inference(forward_demodulation,[],[f32,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f19,f18])).

fof(f19,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f32,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
    inference(definition_unfolding,[],[f20,f18,f18,f18,f18])).

fof(f20,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(X5,k1_tarski(X4))),k2_enumset1(X0,X1,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0))),k4_xboole_0(k4_xboole_0(X5,k1_tarski(X0)),k2_enumset1(X1,X2,X3,X4))) ),
    inference(backward_demodulation,[],[f60,f64])).

fof(f64,plain,(
    ! [X6,X10,X8,X7,X11,X9] : k4_xboole_0(k4_xboole_0(X11,k2_enumset1(X6,X7,X8,X9)),k1_tarski(X10)) = k4_xboole_0(k4_xboole_0(X11,k1_tarski(X6)),k2_enumset1(X7,X8,X9,X10)) ),
    inference(forward_demodulation,[],[f61,f31])).

fof(f61,plain,(
    ! [X6,X10,X8,X7,X11,X9] : k4_xboole_0(k4_xboole_0(X11,k2_enumset1(X6,X7,X8,X9)),k1_tarski(X10)) = k4_xboole_0(X11,k5_xboole_0(k1_tarski(X6),k4_xboole_0(k2_enumset1(X7,X8,X9,X10),k1_tarski(X6)))) ),
    inference(superposition,[],[f31,f33])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(X5,k1_tarski(X4))),k2_enumset1(X0,X1,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0))),k4_xboole_0(k4_xboole_0(X5,k2_enumset1(X0,X1,X2,X3)),k1_tarski(X4))) ),
    inference(superposition,[],[f35,f33])).

fof(f72,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k2_enumset1(sK1,sK2,sK3,sK4))),k1_tarski(sK0)))
    | spl7_1 ),
    inference(superposition,[],[f70,f35])).

fof(f70,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK0)),k2_enumset1(sK1,sK2,sK3,sK4)))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl7_1
  <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK0)),k2_enumset1(sK1,sK2,sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f71,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f34,f68])).

fof(f34,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK0)),k2_enumset1(sK1,sK2,sK3,sK4))) ),
    inference(backward_demodulation,[],[f29,f31])).

fof(f29,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k1_tarski(sK0))))) ),
    inference(definition_unfolding,[],[f15,f28,f18,f26,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f17,f18])).

fof(f17,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f24,f18,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f23,f18,f26])).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

fof(f15,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:26:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (32051)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.47  % (32054)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (32044)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (32046)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (32054)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f71,f77])).
% 0.22/0.48  % (32039)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    spl7_1),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f76])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    $false | spl7_1),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f75])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) | spl7_1),
% 0.22/0.48    inference(forward_demodulation,[],[f74,f58])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ( ! [X6,X8,X7,X5,X9] : (k5_xboole_0(k1_tarski(X9),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k1_tarski(X9))) = k5_xboole_0(k1_tarski(X5),k4_xboole_0(k2_enumset1(X6,X7,X8,X9),k1_tarski(X5)))) )),
% 0.22/0.48    inference(superposition,[],[f33,f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f16,f18,f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0))) = k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f22,f26,f18])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f21,f18])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k1_tarski(sK6))),k1_tarski(sK1))),k1_tarski(sK0))) | spl7_1),
% 0.22/0.48    inference(forward_demodulation,[],[f73,f30])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k4_xboole_0(k1_tarski(sK6),k2_enumset1(sK2,sK3,sK4,sK5))),k1_tarski(sK1))),k1_tarski(sK0))) | spl7_1),
% 0.22/0.48    inference(forward_demodulation,[],[f72,f66])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(X5,k1_tarski(X4))),k2_enumset1(X0,X1,X2,X3))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(X5,k2_enumset1(X1,X2,X3,X4))),k1_tarski(X0)))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f65,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X2,X0),X1))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f32,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f19,f18])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f20,f18,f18,f18,f18])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(X5,k1_tarski(X4))),k2_enumset1(X0,X1,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0))),k4_xboole_0(k4_xboole_0(X5,k1_tarski(X0)),k2_enumset1(X1,X2,X3,X4)))) )),
% 0.22/0.48    inference(backward_demodulation,[],[f60,f64])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    ( ! [X6,X10,X8,X7,X11,X9] : (k4_xboole_0(k4_xboole_0(X11,k2_enumset1(X6,X7,X8,X9)),k1_tarski(X10)) = k4_xboole_0(k4_xboole_0(X11,k1_tarski(X6)),k2_enumset1(X7,X8,X9,X10))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f61,f31])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    ( ! [X6,X10,X8,X7,X11,X9] : (k4_xboole_0(k4_xboole_0(X11,k2_enumset1(X6,X7,X8,X9)),k1_tarski(X10)) = k4_xboole_0(X11,k5_xboole_0(k1_tarski(X6),k4_xboole_0(k2_enumset1(X7,X8,X9,X10),k1_tarski(X6))))) )),
% 0.22/0.48    inference(superposition,[],[f31,f33])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(X5,k1_tarski(X4))),k2_enumset1(X0,X1,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0))),k4_xboole_0(k4_xboole_0(X5,k2_enumset1(X0,X1,X2,X3)),k1_tarski(X4)))) )),
% 0.22/0.48    inference(superposition,[],[f35,f33])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k2_enumset1(sK1,sK2,sK3,sK4))),k1_tarski(sK0))) | spl7_1),
% 0.22/0.48    inference(superposition,[],[f70,f35])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK0)),k2_enumset1(sK1,sK2,sK3,sK4))) | spl7_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f68])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    spl7_1 <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK0)),k2_enumset1(sK1,sK2,sK3,sK4)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    ~spl7_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f34,f68])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK0)),k2_enumset1(sK1,sK2,sK3,sK4)))),
% 0.22/0.48    inference(backward_demodulation,[],[f29,f31])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k1_tarski(sK0)))))),
% 0.22/0.48    inference(definition_unfolding,[],[f15,f28,f18,f26,f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f17,f18])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f24,f18,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f23,f18,f26])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f12,f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.22/0.48    inference(negated_conjecture,[],[f10])).
% 0.22/0.48  fof(f10,conjecture,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (32054)------------------------------
% 0.22/0.48  % (32054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (32054)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (32043)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (32054)Memory used [KB]: 10746
% 0.22/0.48  % (32054)Time elapsed: 0.011 s
% 0.22/0.48  % (32054)------------------------------
% 0.22/0.48  % (32054)------------------------------
% 0.22/0.48  % (32056)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.48  % (32040)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (32038)Success in time 0.123 s
%------------------------------------------------------------------------------
