%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 101 expanded)
%              Number of leaves         :   15 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 ( 132 expanded)
%              Number of equality atoms :   45 (  95 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f70,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f49,f57,f69])).

fof(f69,plain,
    ( ~ spl6_1
    | spl6_2
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | ~ spl6_4 ),
    inference(trivial_inequality_removal,[],[f67])).

fof(f67,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k5_xboole_0(k1_enumset1(sK3,sK4,sK5),k3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)))) != k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k5_xboole_0(k1_enumset1(sK3,sK4,sK5),k3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5))))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f66,f39])).

fof(f39,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl6_1
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f66,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k5_xboole_0(k1_enumset1(sK3,sK4,sK5),k3_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_enumset1(sK0,sK1,sK2)))) != k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k5_xboole_0(k1_enumset1(sK3,sK4,sK5),k3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5))))
    | spl6_2
    | ~ spl6_4 ),
    inference(superposition,[],[f44,f56])).

fof(f56,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_enumset1(X3,X4,X0),k5_xboole_0(k1_enumset1(X1,X2,X5),k3_xboole_0(k1_enumset1(X1,X2,X5),k1_enumset1(X3,X4,X0)))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X4),k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2)))),k5_xboole_0(k1_enumset1(X5,X5,X5),k3_xboole_0(k1_enumset1(X5,X5,X5),k5_xboole_0(k1_enumset1(X3,X3,X4),k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2)))))))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl6_4
  <=> ! [X1,X3,X5,X0,X2,X4] : k5_xboole_0(k1_enumset1(X3,X4,X0),k5_xboole_0(k1_enumset1(X1,X2,X5),k3_xboole_0(k1_enumset1(X1,X2,X5),k1_enumset1(X3,X4,X0)))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X4),k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2)))),k5_xboole_0(k1_enumset1(X5,X5,X5),k3_xboole_0(k1_enumset1(X5,X5,X5),k5_xboole_0(k1_enumset1(X3,X3,X4),k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f44,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK3,sK4)))),k5_xboole_0(k1_enumset1(sK5,sK5,sK5),k3_xboole_0(k1_enumset1(sK5,sK5,sK5),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK3,sK4))))))) != k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k5_xboole_0(k1_enumset1(sK3,sK4,sK5),k3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5))))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl6_2
  <=> k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK3,sK4)))),k5_xboole_0(k1_enumset1(sK5,sK5,sK5),k3_xboole_0(k1_enumset1(sK5,sK5,sK5),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK3,sK4))))))) = k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k5_xboole_0(k1_enumset1(sK3,sK4,sK5),k3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f57,plain,
    ( spl6_4
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f50,f47,f38,f55])).

fof(f47,plain,
    ( spl6_3
  <=> ! [X1,X3,X5,X0,X2,X4] : k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2)))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))),k5_xboole_0(k1_enumset1(X5,X5,X5),k3_xboole_0(k1_enumset1(X5,X5,X5),k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f50,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_enumset1(X3,X4,X0),k5_xboole_0(k1_enumset1(X1,X2,X5),k3_xboole_0(k1_enumset1(X1,X2,X5),k1_enumset1(X3,X4,X0)))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X4),k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2)))),k5_xboole_0(k1_enumset1(X5,X5,X5),k3_xboole_0(k1_enumset1(X5,X5,X5),k5_xboole_0(k1_enumset1(X3,X3,X4),k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2)))))))
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(superposition,[],[f48,f39])).

fof(f48,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2)))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))),k5_xboole_0(k1_enumset1(X5,X5,X5),k3_xboole_0(k1_enumset1(X5,X5,X5),k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))))))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f49,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f34,f47])).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2)))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))),k5_xboole_0(k1_enumset1(X5,X5,X5),k3_xboole_0(k1_enumset1(X5,X5,X5),k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1))))))) ),
    inference(definition_unfolding,[],[f24,f28,f27,f29,f30])).

fof(f30,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f17,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f17,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f22,f27,f19])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f21,f20])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2)))) ),
    inference(definition_unfolding,[],[f23,f27])).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(f45,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f36,f42])).

fof(f36,plain,(
    k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK3,sK4)))),k5_xboole_0(k1_enumset1(sK5,sK5,sK5),k3_xboole_0(k1_enumset1(sK5,sK5,sK5),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK3,sK4))))))) != k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k5_xboole_0(k1_enumset1(sK3,sK4,sK5),k3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)))) ),
    inference(forward_demodulation,[],[f35,f18])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f35,plain,(
    k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k5_xboole_0(k1_enumset1(sK3,sK4,sK5),k3_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_enumset1(sK0,sK1,sK2)))) != k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK3,sK4)))),k5_xboole_0(k1_enumset1(sK5,sK5,sK5),k3_xboole_0(k1_enumset1(sK5,sK5,sK5),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK3,sK4))))))) ),
    inference(backward_demodulation,[],[f33,f18])).

fof(f33,plain,(
    k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k5_xboole_0(k1_enumset1(sK3,sK4,sK5),k3_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_enumset1(sK0,sK1,sK2)))) != k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_enumset1(sK0,sK0,sK1)))),k5_xboole_0(k1_enumset1(sK5,sK5,sK5),k3_xboole_0(k1_enumset1(sK5,sK5,sK5),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_enumset1(sK0,sK0,sK1))))))) ),
    inference(definition_unfolding,[],[f16,f28,f31])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2)))),k5_xboole_0(k1_enumset1(X6,X6,X6),k3_xboole_0(k1_enumset1(X6,X6,X6),k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2))))))) ),
    inference(definition_unfolding,[],[f25,f27,f28,f30])).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

fof(f16,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k5_enumset1(X0,X0,X1,X2,X3,X4,X5)
   => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f40,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f18,f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:46:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (4486)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (4494)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.46  % (4494)Refutation not found, incomplete strategy% (4494)------------------------------
% 0.20/0.46  % (4494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (4494)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (4494)Memory used [KB]: 10490
% 0.20/0.46  % (4494)Time elapsed: 0.006 s
% 0.20/0.46  % (4494)------------------------------
% 0.20/0.46  % (4494)------------------------------
% 0.20/0.46  % (4490)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (4490)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f70,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f40,f45,f49,f57,f69])).
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    ~spl6_1 | spl6_2 | ~spl6_4),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f68])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    $false | (~spl6_1 | spl6_2 | ~spl6_4)),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f67])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k5_xboole_0(k1_enumset1(sK3,sK4,sK5),k3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)))) != k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k5_xboole_0(k1_enumset1(sK3,sK4,sK5),k3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)))) | (~spl6_1 | spl6_2 | ~spl6_4)),
% 0.20/0.46    inference(forward_demodulation,[],[f66,f39])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl6_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    spl6_1 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k5_xboole_0(k1_enumset1(sK3,sK4,sK5),k3_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_enumset1(sK0,sK1,sK2)))) != k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k5_xboole_0(k1_enumset1(sK3,sK4,sK5),k3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)))) | (spl6_2 | ~spl6_4)),
% 0.20/0.47    inference(superposition,[],[f44,f56])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_enumset1(X3,X4,X0),k5_xboole_0(k1_enumset1(X1,X2,X5),k3_xboole_0(k1_enumset1(X1,X2,X5),k1_enumset1(X3,X4,X0)))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X4),k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2)))),k5_xboole_0(k1_enumset1(X5,X5,X5),k3_xboole_0(k1_enumset1(X5,X5,X5),k5_xboole_0(k1_enumset1(X3,X3,X4),k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2)))))))) ) | ~spl6_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f55])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    spl6_4 <=> ! [X1,X3,X5,X0,X2,X4] : k5_xboole_0(k1_enumset1(X3,X4,X0),k5_xboole_0(k1_enumset1(X1,X2,X5),k3_xboole_0(k1_enumset1(X1,X2,X5),k1_enumset1(X3,X4,X0)))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X4),k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2)))),k5_xboole_0(k1_enumset1(X5,X5,X5),k3_xboole_0(k1_enumset1(X5,X5,X5),k5_xboole_0(k1_enumset1(X3,X3,X4),k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2)))))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK3,sK4)))),k5_xboole_0(k1_enumset1(sK5,sK5,sK5),k3_xboole_0(k1_enumset1(sK5,sK5,sK5),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK3,sK4))))))) != k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k5_xboole_0(k1_enumset1(sK3,sK4,sK5),k3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)))) | spl6_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    spl6_2 <=> k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK3,sK4)))),k5_xboole_0(k1_enumset1(sK5,sK5,sK5),k3_xboole_0(k1_enumset1(sK5,sK5,sK5),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK3,sK4))))))) = k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k5_xboole_0(k1_enumset1(sK3,sK4,sK5),k3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    spl6_4 | ~spl6_1 | ~spl6_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f50,f47,f38,f55])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    spl6_3 <=> ! [X1,X3,X5,X0,X2,X4] : k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2)))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))),k5_xboole_0(k1_enumset1(X5,X5,X5),k3_xboole_0(k1_enumset1(X5,X5,X5),k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_enumset1(X3,X4,X0),k5_xboole_0(k1_enumset1(X1,X2,X5),k3_xboole_0(k1_enumset1(X1,X2,X5),k1_enumset1(X3,X4,X0)))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X4),k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2)))),k5_xboole_0(k1_enumset1(X5,X5,X5),k3_xboole_0(k1_enumset1(X5,X5,X5),k5_xboole_0(k1_enumset1(X3,X3,X4),k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2)))))))) ) | (~spl6_1 | ~spl6_3)),
% 0.20/0.47    inference(superposition,[],[f48,f39])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2)))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))),k5_xboole_0(k1_enumset1(X5,X5,X5),k3_xboole_0(k1_enumset1(X5,X5,X5),k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))))))) ) | ~spl6_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f47])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    spl6_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f34,f47])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2)))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))),k5_xboole_0(k1_enumset1(X5,X5,X5),k3_xboole_0(k1_enumset1(X5,X5,X5),k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))))))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f24,f28,f27,f29,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f17,f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1))))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f22,f27,f19])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f21,f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2))))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f23,f27])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ~spl6_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f36,f42])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK3,sK4)))),k5_xboole_0(k1_enumset1(sK5,sK5,sK5),k3_xboole_0(k1_enumset1(sK5,sK5,sK5),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK3,sK4))))))) != k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k5_xboole_0(k1_enumset1(sK3,sK4,sK5),k3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5))))),
% 0.20/0.47    inference(forward_demodulation,[],[f35,f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k5_xboole_0(k1_enumset1(sK3,sK4,sK5),k3_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_enumset1(sK0,sK1,sK2)))) != k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK3,sK4)))),k5_xboole_0(k1_enumset1(sK5,sK5,sK5),k3_xboole_0(k1_enumset1(sK5,sK5,sK5),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK3,sK4)))))))),
% 0.20/0.47    inference(backward_demodulation,[],[f33,f18])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k5_xboole_0(k1_enumset1(sK3,sK4,sK5),k3_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_enumset1(sK0,sK1,sK2)))) != k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_enumset1(sK0,sK0,sK1)))),k5_xboole_0(k1_enumset1(sK5,sK5,sK5),k3_xboole_0(k1_enumset1(sK5,sK5,sK5),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_enumset1(sK0,sK0,sK1)))))))),
% 0.20/0.47    inference(definition_unfolding,[],[f16,f28,f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2)))),k5_xboole_0(k1_enumset1(X6,X6,X6),k3_xboole_0(k1_enumset1(X6,X6,X6),k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2)))))))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f25,f27,f28,f30])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5)),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f13,f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k5_enumset1(X0,X0,X1,X2,X3,X4,X5) => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5)),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.20/0.47    inference(negated_conjecture,[],[f11])).
% 0.20/0.47  fof(f11,conjecture,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    spl6_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f18,f38])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (4490)------------------------------
% 0.20/0.47  % (4490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (4490)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (4490)Memory used [KB]: 6268
% 0.20/0.47  % (4490)Time elapsed: 0.047 s
% 0.20/0.47  % (4490)------------------------------
% 0.20/0.47  % (4490)------------------------------
% 0.20/0.47  % (4482)Success in time 0.114 s
%------------------------------------------------------------------------------
