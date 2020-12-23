%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 159 expanded)
%              Number of leaves         :   11 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :   52 ( 165 expanded)
%              Number of equality atoms :   44 ( 156 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f537,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f536])).

fof(f536,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f535])).

fof(f535,plain,
    ( $false
    | spl7_1 ),
    inference(subsumption_resolution,[],[f447,f135])).

fof(f135,plain,(
    ! [X12,X10,X8,X7,X13,X11,X9] : k5_xboole_0(k1_tarski(X7),k4_xboole_0(k4_enumset1(X8,X9,X10,X11,X12,X13),k1_tarski(X7))) = k5_xboole_0(k1_tarski(X7),k4_xboole_0(k5_xboole_0(k1_tarski(X8),k4_xboole_0(k5_xboole_0(k1_tarski(X9),k4_xboole_0(k2_enumset1(X10,X11,X12,X13),k1_tarski(X9))),k1_tarski(X8))),k1_tarski(X7))) ),
    inference(superposition,[],[f40,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X2,X0),X1)) ),
    inference(forward_demodulation,[],[f34,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f21,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f21,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
    inference(definition_unfolding,[],[f22,f19,f19,f19,f19])).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X2))),k1_tarski(X0)),k1_tarski(X1))) ),
    inference(forward_demodulation,[],[f35,f33])).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))) ),
    inference(definition_unfolding,[],[f25,f27,f19,f28,f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f23,f19])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f18,f19])).

fof(f18,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f24,f19])).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).

fof(f447,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl7_1 ),
    inference(superposition,[],[f66,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0)) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X3,X0)),X2)),X1)) ),
    inference(forward_demodulation,[],[f55,f39])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0)) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X3,X0)),X1),X2)) ),
    inference(forward_demodulation,[],[f54,f33])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X3,X0)),k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0)) ),
    inference(forward_demodulation,[],[f53,f39])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X3,X0)),k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0)) ),
    inference(forward_demodulation,[],[f48,f33])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X3,X0)),k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X2)),k4_xboole_0(k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))),X0)) ),
    inference(superposition,[],[f39,f33])).

fof(f66,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl7_1
  <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f67,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f38,f64])).

fof(f38,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))) ),
    inference(forward_demodulation,[],[f37,f33])).

fof(f37,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK0)),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))) ),
    inference(backward_demodulation,[],[f31,f33])).

fof(f31,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))))) ),
    inference(definition_unfolding,[],[f16,f27,f19,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f20,f19,f28])).

fof(f20,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f16,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (12812)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.46  % (12803)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (12806)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (12810)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (12811)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.47  % (12817)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (12819)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (12807)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (12805)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (12820)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (12816)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (12809)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (12813)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (12818)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (12814)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (12814)Refutation not found, incomplete strategy% (12814)------------------------------
% 0.21/0.50  % (12814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12814)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (12814)Memory used [KB]: 10618
% 0.21/0.50  % (12814)Time elapsed: 0.090 s
% 0.21/0.50  % (12814)------------------------------
% 0.21/0.50  % (12814)------------------------------
% 0.21/0.50  % (12815)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (12808)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (12804)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.55  % (12818)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f537,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f67,f536])).
% 0.21/0.55  fof(f536,plain,(
% 0.21/0.55    spl7_1),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f535])).
% 0.21/0.55  fof(f535,plain,(
% 0.21/0.55    $false | spl7_1),
% 0.21/0.55    inference(subsumption_resolution,[],[f447,f135])).
% 0.21/0.55  fof(f135,plain,(
% 0.21/0.55    ( ! [X12,X10,X8,X7,X13,X11,X9] : (k5_xboole_0(k1_tarski(X7),k4_xboole_0(k4_enumset1(X8,X9,X10,X11,X12,X13),k1_tarski(X7))) = k5_xboole_0(k1_tarski(X7),k4_xboole_0(k5_xboole_0(k1_tarski(X8),k4_xboole_0(k5_xboole_0(k1_tarski(X9),k4_xboole_0(k2_enumset1(X10,X11,X12,X13),k1_tarski(X9))),k1_tarski(X8))),k1_tarski(X7)))) )),
% 0.21/0.55    inference(superposition,[],[f40,f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X2,X0),X1))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f34,f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f21,f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f22,f19,f19,f19,f19])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X2))),k1_tarski(X0)),k1_tarski(X1)))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f35,f33])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f25,f27,f19,f28,f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0)))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f23,f19])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f18,f19])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0)))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f24,f19])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).
% 0.21/0.55  fof(f447,plain,(
% 0.21/0.55    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) | spl7_1),
% 0.21/0.55    inference(superposition,[],[f66,f56])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0)) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X3,X0)),X2)),X1))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f55,f39])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0)) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X3,X0)),X1),X2))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f54,f33])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X3,X0)),k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f53,f39])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X3,X0)),k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f48,f33])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X3,X0)),k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X2)),k4_xboole_0(k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))),X0))) )),
% 0.21/0.55    inference(superposition,[],[f39,f33])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))) | spl7_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    spl7_1 <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    ~spl7_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f38,f64])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)))),
% 0.21/0.55    inference(forward_demodulation,[],[f37,f33])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK0)),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))))),
% 0.21/0.55    inference(backward_demodulation,[],[f31,f33])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0)))))),
% 0.21/0.55    inference(definition_unfolding,[],[f16,f27,f19,f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f20,f19,f28])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6))),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f13,f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.21/0.55    inference(ennf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.21/0.55    inference(negated_conjecture,[],[f11])).
% 0.21/0.55  fof(f11,conjecture,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (12818)------------------------------
% 0.21/0.55  % (12818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (12818)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (12818)Memory used [KB]: 11769
% 0.21/0.55  % (12818)Time elapsed: 0.113 s
% 0.21/0.55  % (12818)------------------------------
% 0.21/0.55  % (12818)------------------------------
% 0.21/0.55  % (12802)Success in time 0.197 s
%------------------------------------------------------------------------------
