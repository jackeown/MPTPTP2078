%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 156 expanded)
%              Number of leaves         :   12 (  63 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 ( 165 expanded)
%              Number of equality atoms :   40 ( 153 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f70,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f69])).

fof(f69,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | spl9_1 ),
    inference(subsumption_resolution,[],[f67,f38])).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k5_xboole_0(k1_enumset1(X2,X3,X4),k4_xboole_0(k5_xboole_0(k1_enumset1(X5,X5,X6),k4_xboole_0(k1_enumset1(X7,X7,X8),k1_enumset1(X5,X5,X6))),k1_enumset1(X2,X3,X4))),k1_enumset1(X0,X0,X1))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X4),k4_xboole_0(k5_xboole_0(k1_enumset1(X5,X5,X6),k4_xboole_0(k1_enumset1(X7,X7,X8),k1_enumset1(X5,X5,X6))),k1_enumset1(X3,X3,X4))),k1_enumset1(X0,X1,X2))) ),
    inference(definition_unfolding,[],[f28,f31,f21,f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X3),k4_xboole_0(k1_enumset1(X4,X4,X5),k1_enumset1(X2,X2,X3))),k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f25,f30])).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X4),k4_xboole_0(k1_enumset1(X5,X5,X6),k1_enumset1(X3,X3,X4))),k1_enumset1(X0,X1,X2))) ),
    inference(definition_unfolding,[],[f26,f21,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f24,f21,f19,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k5_xboole_0(k1_enumset1(X2,X3,X4),k4_xboole_0(k5_xboole_0(k1_enumset1(X5,X5,X6),k4_xboole_0(k1_enumset1(X7,X7,X8),k1_enumset1(X5,X5,X6))),k1_enumset1(X2,X3,X4))),k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f27,f21,f19,f30])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_enumset1)).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_enumset1)).

fof(f67,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k4_xboole_0(k5_xboole_0(k1_enumset1(sK5,sK5,sK6),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k1_enumset1(sK5,sK5,sK6))),k1_enumset1(sK2,sK3,sK4))),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k4_xboole_0(k5_xboole_0(k1_enumset1(sK5,sK5,sK6),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k1_enumset1(sK5,sK5,sK6))),k1_enumset1(sK3,sK3,sK4))),k1_enumset1(sK0,sK1,sK2)))
    | spl9_1 ),
    inference(forward_demodulation,[],[f66,f52])).

fof(f52,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),X3)) = k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X4,X3)),X5)) ),
    inference(superposition,[],[f37,f35])).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f18,f21,f21])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f37,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
    inference(definition_unfolding,[],[f23,f21,f21,f21,f21])).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f66,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k4_xboole_0(k5_xboole_0(k1_enumset1(sK5,sK5,sK6),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k1_enumset1(sK5,sK5,sK6))),k1_enumset1(sK2,sK3,sK4))),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_enumset1(sK5,sK5,sK6),k4_xboole_0(k5_xboole_0(k1_enumset1(sK7,sK7,sK8),k4_xboole_0(k1_enumset1(sK3,sK3,sK4),k1_enumset1(sK7,sK7,sK8))),k1_enumset1(sK5,sK5,sK6))),k1_enumset1(sK0,sK1,sK2)))
    | spl9_1 ),
    inference(forward_demodulation,[],[f65,f52])).

fof(f65,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k4_xboole_0(k5_xboole_0(k1_enumset1(sK5,sK5,sK6),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k1_enumset1(sK5,sK5,sK6))),k1_enumset1(sK2,sK3,sK4))),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_enumset1(sK7,sK7,sK8),k4_xboole_0(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k4_xboole_0(k1_enumset1(sK5,sK5,sK6),k1_enumset1(sK3,sK3,sK4))),k1_enumset1(sK7,sK7,sK8))),k1_enumset1(sK0,sK1,sK2)))
    | spl9_1 ),
    inference(forward_demodulation,[],[f62,f35])).

fof(f62,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k4_xboole_0(k5_xboole_0(k1_enumset1(sK5,sK5,sK6),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k1_enumset1(sK5,sK5,sK6))),k1_enumset1(sK2,sK3,sK4))),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k4_xboole_0(k1_enumset1(sK5,sK5,sK6),k1_enumset1(sK3,sK3,sK4))),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k4_xboole_0(k1_enumset1(sK5,sK5,sK6),k1_enumset1(sK3,sK3,sK4))))),k1_enumset1(sK0,sK1,sK2)))
    | spl9_1 ),
    inference(superposition,[],[f60,f37])).

fof(f60,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k4_xboole_0(k5_xboole_0(k1_enumset1(sK5,sK5,sK6),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k1_enumset1(sK5,sK5,sK6))),k1_enumset1(sK2,sK3,sK4))),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k4_xboole_0(k1_enumset1(sK5,sK5,sK6),k1_enumset1(sK3,sK3,sK4))),k1_enumset1(sK0,sK1,sK2))),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k4_xboole_0(k1_enumset1(sK5,sK5,sK6),k1_enumset1(sK3,sK3,sK4))),k1_enumset1(sK0,sK1,sK2)))))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl9_1
  <=> k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k4_xboole_0(k5_xboole_0(k1_enumset1(sK5,sK5,sK6),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k1_enumset1(sK5,sK5,sK6))),k1_enumset1(sK2,sK3,sK4))),k1_enumset1(sK0,sK0,sK1))) = k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k4_xboole_0(k1_enumset1(sK5,sK5,sK6),k1_enumset1(sK3,sK3,sK4))),k1_enumset1(sK0,sK1,sK2))),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k4_xboole_0(k1_enumset1(sK5,sK5,sK6),k1_enumset1(sK3,sK3,sK4))),k1_enumset1(sK0,sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f61,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f34,f58])).

% (3735)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
fof(f34,plain,(
    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k4_xboole_0(k5_xboole_0(k1_enumset1(sK5,sK5,sK6),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k1_enumset1(sK5,sK5,sK6))),k1_enumset1(sK2,sK3,sK4))),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k4_xboole_0(k1_enumset1(sK5,sK5,sK6),k1_enumset1(sK3,sK3,sK4))),k1_enumset1(sK0,sK1,sK2))),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k4_xboole_0(k1_enumset1(sK5,sK5,sK6),k1_enumset1(sK3,sK3,sK4))),k1_enumset1(sK0,sK1,sK2))))) ),
    inference(definition_unfolding,[],[f17,f31,f21,f30,f19])).

fof(f17,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k2_tarski(sK7,sK8)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k2_tarski(sK7,sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))
   => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k2_tarski(sK7,sK8)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (3733)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.46  % (3721)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (3722)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (3725)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (3734)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (3726)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (3728)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (3723)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (3729)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (3732)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (3732)Refutation not found, incomplete strategy% (3732)------------------------------
% 0.21/0.48  % (3732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3732)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (3732)Memory used [KB]: 10618
% 0.21/0.48  % (3732)Time elapsed: 0.076 s
% 0.21/0.48  % (3732)------------------------------
% 0.21/0.48  % (3732)------------------------------
% 0.21/0.48  % (3736)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (3736)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f61,f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    spl9_1),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    $false | spl9_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f67,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k5_xboole_0(k1_enumset1(X2,X3,X4),k4_xboole_0(k5_xboole_0(k1_enumset1(X5,X5,X6),k4_xboole_0(k1_enumset1(X7,X7,X8),k1_enumset1(X5,X5,X6))),k1_enumset1(X2,X3,X4))),k1_enumset1(X0,X0,X1))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X4),k4_xboole_0(k5_xboole_0(k1_enumset1(X5,X5,X6),k4_xboole_0(k1_enumset1(X7,X7,X8),k1_enumset1(X5,X5,X6))),k1_enumset1(X3,X3,X4))),k1_enumset1(X0,X1,X2)))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f28,f31,f21,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X3),k4_xboole_0(k1_enumset1(X4,X4,X5),k1_enumset1(X2,X2,X3))),k1_enumset1(X0,X0,X1)))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f25,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X4),k4_xboole_0(k1_enumset1(X5,X5,X6),k1_enumset1(X3,X3,X4))),k1_enumset1(X0,X1,X2)))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f26,f21,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f24,f21,f19,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k5_xboole_0(k1_enumset1(X2,X3,X4),k4_xboole_0(k5_xboole_0(k1_enumset1(X5,X5,X6),k4_xboole_0(k1_enumset1(X7,X7,X8),k1_enumset1(X5,X5,X6))),k1_enumset1(X2,X3,X4))),k1_enumset1(X0,X0,X1)))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f27,f21,f19,f30])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_enumset1)).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_enumset1)).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k4_xboole_0(k5_xboole_0(k1_enumset1(sK5,sK5,sK6),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k1_enumset1(sK5,sK5,sK6))),k1_enumset1(sK2,sK3,sK4))),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k4_xboole_0(k5_xboole_0(k1_enumset1(sK5,sK5,sK6),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k1_enumset1(sK5,sK5,sK6))),k1_enumset1(sK3,sK3,sK4))),k1_enumset1(sK0,sK1,sK2))) | spl9_1),
% 0.21/0.49    inference(forward_demodulation,[],[f66,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),X3)) = k5_xboole_0(X5,k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X4,X3)),X5))) )),
% 0.21/0.49    inference(superposition,[],[f37,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f18,f21,f21])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f23,f21,f21,f21,f21])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k4_xboole_0(k5_xboole_0(k1_enumset1(sK5,sK5,sK6),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k1_enumset1(sK5,sK5,sK6))),k1_enumset1(sK2,sK3,sK4))),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_enumset1(sK5,sK5,sK6),k4_xboole_0(k5_xboole_0(k1_enumset1(sK7,sK7,sK8),k4_xboole_0(k1_enumset1(sK3,sK3,sK4),k1_enumset1(sK7,sK7,sK8))),k1_enumset1(sK5,sK5,sK6))),k1_enumset1(sK0,sK1,sK2))) | spl9_1),
% 0.21/0.49    inference(forward_demodulation,[],[f65,f52])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k4_xboole_0(k5_xboole_0(k1_enumset1(sK5,sK5,sK6),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k1_enumset1(sK5,sK5,sK6))),k1_enumset1(sK2,sK3,sK4))),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_enumset1(sK7,sK7,sK8),k4_xboole_0(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k4_xboole_0(k1_enumset1(sK5,sK5,sK6),k1_enumset1(sK3,sK3,sK4))),k1_enumset1(sK7,sK7,sK8))),k1_enumset1(sK0,sK1,sK2))) | spl9_1),
% 0.21/0.49    inference(forward_demodulation,[],[f62,f35])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k4_xboole_0(k5_xboole_0(k1_enumset1(sK5,sK5,sK6),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k1_enumset1(sK5,sK5,sK6))),k1_enumset1(sK2,sK3,sK4))),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k4_xboole_0(k1_enumset1(sK5,sK5,sK6),k1_enumset1(sK3,sK3,sK4))),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k4_xboole_0(k1_enumset1(sK5,sK5,sK6),k1_enumset1(sK3,sK3,sK4))))),k1_enumset1(sK0,sK1,sK2))) | spl9_1),
% 0.21/0.49    inference(superposition,[],[f60,f37])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k4_xboole_0(k5_xboole_0(k1_enumset1(sK5,sK5,sK6),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k1_enumset1(sK5,sK5,sK6))),k1_enumset1(sK2,sK3,sK4))),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k4_xboole_0(k1_enumset1(sK5,sK5,sK6),k1_enumset1(sK3,sK3,sK4))),k1_enumset1(sK0,sK1,sK2))),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k4_xboole_0(k1_enumset1(sK5,sK5,sK6),k1_enumset1(sK3,sK3,sK4))),k1_enumset1(sK0,sK1,sK2))))) | spl9_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    spl9_1 <=> k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k4_xboole_0(k5_xboole_0(k1_enumset1(sK5,sK5,sK6),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k1_enumset1(sK5,sK5,sK6))),k1_enumset1(sK2,sK3,sK4))),k1_enumset1(sK0,sK0,sK1))) = k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k4_xboole_0(k1_enumset1(sK5,sK5,sK6),k1_enumset1(sK3,sK3,sK4))),k1_enumset1(sK0,sK1,sK2))),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k4_xboole_0(k1_enumset1(sK5,sK5,sK6),k1_enumset1(sK3,sK3,sK4))),k1_enumset1(sK0,sK1,sK2)))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ~spl9_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f34,f58])).
% 0.21/0.49  % (3735)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k4_xboole_0(k5_xboole_0(k1_enumset1(sK5,sK5,sK6),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k1_enumset1(sK5,sK5,sK6))),k1_enumset1(sK2,sK3,sK4))),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k4_xboole_0(k1_enumset1(sK5,sK5,sK6),k1_enumset1(sK3,sK3,sK4))),k1_enumset1(sK0,sK1,sK2))),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k4_xboole_0(k1_enumset1(sK5,sK5,sK6),k1_enumset1(sK3,sK3,sK4))),k1_enumset1(sK0,sK1,sK2)))))),
% 0.21/0.49    inference(definition_unfolding,[],[f17,f31,f21,f30,f19])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k2_tarski(sK7,sK8))),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k2_tarski(sK7,sK8))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f14,f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k2_tarski(sK7,sK8))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))),
% 0.21/0.49    inference(negated_conjecture,[],[f12])).
% 0.21/0.49  fof(f12,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (3736)------------------------------
% 0.21/0.49  % (3736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (3736)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (3736)Memory used [KB]: 10746
% 0.21/0.49  % (3736)Time elapsed: 0.083 s
% 0.21/0.49  % (3736)------------------------------
% 0.21/0.49  % (3736)------------------------------
% 0.21/0.49  % (3720)Success in time 0.134 s
%------------------------------------------------------------------------------
