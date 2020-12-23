%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 119 expanded)
%              Number of leaves         :   10 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :   50 ( 138 expanded)
%              Number of equality atoms :   34 ( 115 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f48,f96])).

fof(f96,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f30,f79])).

fof(f79,plain,
    ( ! [X21,X19,X17,X20,X18] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X20,k5_xboole_0(k5_xboole_0(X21,X17),k3_xboole_0(X21,X17))),k3_xboole_0(X20,k5_xboole_0(k5_xboole_0(X21,X17),k3_xboole_0(X21,X17)))),k5_xboole_0(k5_xboole_0(X18,X19),k3_xboole_0(X18,X19))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X20,k5_xboole_0(k5_xboole_0(X21,X17),k3_xboole_0(X21,X17))),k3_xboole_0(X20,k5_xboole_0(k5_xboole_0(X21,X17),k3_xboole_0(X21,X17)))),k5_xboole_0(k5_xboole_0(X18,X19),k3_xboole_0(X18,X19)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X20,X21),k3_xboole_0(X20,X21)),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X17,X18),k3_xboole_0(X17,X18)),X19),k3_xboole_0(k5_xboole_0(k5_xboole_0(X17,X18),k3_xboole_0(X17,X18)),X19))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X20,X21),k3_xboole_0(X20,X21)),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X17,X18),k3_xboole_0(X17,X18)),X19),k3_xboole_0(k5_xboole_0(k5_xboole_0(X17,X18),k3_xboole_0(X17,X18)),X19))))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(superposition,[],[f47,f33])).

fof(f33,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl6_1
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f47,plain,
    ( ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)))),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)))),X3)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3))))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl6_2
  <=> ! [X1,X3,X0,X2] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)))),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)))),X3)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f30,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k3_xboole_0(k1_tarski(sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k3_xboole_0(k1_tarski(sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))))))) ),
    inference(forward_demodulation,[],[f29,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f17,f15,f15,f15,f15])).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f17,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f29,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k3_xboole_0(k1_tarski(sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k3_xboole_0(k1_tarski(sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))))))) ),
    inference(forward_demodulation,[],[f28,f26])).

fof(f28,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5))))) ),
    inference(backward_demodulation,[],[f25,f26])).

fof(f25,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5))))) ),
    inference(definition_unfolding,[],[f13,f23,f15,f21,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3))) ),
    inference(definition_unfolding,[],[f18,f15,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))) ),
    inference(definition_unfolding,[],[f16,f15,f21])).

fof(f16,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))) ),
    inference(definition_unfolding,[],[f14,f15])).

fof(f14,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X3),k1_tarski(X4)),k3_xboole_0(k1_tarski(X3),k1_tarski(X4))),k1_tarski(X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X3),k1_tarski(X4)),k3_xboole_0(k1_tarski(X3),k1_tarski(X4))),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X3),k1_tarski(X4)),k3_xboole_0(k1_tarski(X3),k1_tarski(X4))),k1_tarski(X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X3),k1_tarski(X4)),k3_xboole_0(k1_tarski(X3),k1_tarski(X4))),k1_tarski(X5))))) ),
    inference(definition_unfolding,[],[f20,f15,f22,f22])).

fof(f20,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

fof(f13,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_tarski(sK0,sK1),k2_enumset1(sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_tarski(sK0,sK1),k2_enumset1(sK2,sK3,sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))
   => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_tarski(sK0,sK1),k2_enumset1(sK2,sK3,sK4,sK5)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_enumset1)).

fof(f48,plain,
    ( spl6_2
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f37,f32,f46])).

fof(f37,plain,
    ( ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)))),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)))),X3)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3))))
    | ~ spl6_1 ),
    inference(superposition,[],[f33,f33])).

fof(f34,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f26,f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:45:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (20181)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.44  % (20184)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (20183)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (20184)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f34,f48,f96])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    ~spl6_1 | ~spl6_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f95])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    $false | (~spl6_1 | ~spl6_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f30,f79])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    ( ! [X21,X19,X17,X20,X18] : (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X20,k5_xboole_0(k5_xboole_0(X21,X17),k3_xboole_0(X21,X17))),k3_xboole_0(X20,k5_xboole_0(k5_xboole_0(X21,X17),k3_xboole_0(X21,X17)))),k5_xboole_0(k5_xboole_0(X18,X19),k3_xboole_0(X18,X19))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X20,k5_xboole_0(k5_xboole_0(X21,X17),k3_xboole_0(X21,X17))),k3_xboole_0(X20,k5_xboole_0(k5_xboole_0(X21,X17),k3_xboole_0(X21,X17)))),k5_xboole_0(k5_xboole_0(X18,X19),k3_xboole_0(X18,X19)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X20,X21),k3_xboole_0(X20,X21)),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X17,X18),k3_xboole_0(X17,X18)),X19),k3_xboole_0(k5_xboole_0(k5_xboole_0(X17,X18),k3_xboole_0(X17,X18)),X19))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X20,X21),k3_xboole_0(X20,X21)),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X17,X18),k3_xboole_0(X17,X18)),X19),k3_xboole_0(k5_xboole_0(k5_xboole_0(X17,X18),k3_xboole_0(X17,X18)),X19))))) ) | (~spl6_1 | ~spl6_2)),
% 0.21/0.47    inference(superposition,[],[f47,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))))) ) | ~spl6_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    spl6_1 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)))),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)))),X3)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3))))) ) | ~spl6_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    spl6_2 <=> ! [X1,X3,X0,X2] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)))),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)))),X3)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k3_xboole_0(k1_tarski(sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k3_xboole_0(k1_tarski(sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))))),
% 0.21/0.47    inference(forward_demodulation,[],[f29,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f17,f15,f15,f15,f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k3_xboole_0(k1_tarski(sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k3_xboole_0(k1_tarski(sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))))),
% 0.21/0.47    inference(forward_demodulation,[],[f28,f26])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)))))),
% 0.21/0.47    inference(backward_demodulation,[],[f25,f26])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)))))),
% 0.21/0.47    inference(definition_unfolding,[],[f13,f23,f15,f21,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f18,f15,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f16,f15,f21])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f14,f15])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X3),k1_tarski(X4)),k3_xboole_0(k1_tarski(X3),k1_tarski(X4))),k1_tarski(X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X3),k1_tarski(X4)),k3_xboole_0(k1_tarski(X3),k1_tarski(X4))),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X3),k1_tarski(X4)),k3_xboole_0(k1_tarski(X3),k1_tarski(X4))),k1_tarski(X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X3),k1_tarski(X4)),k3_xboole_0(k1_tarski(X3),k1_tarski(X4))),k1_tarski(X5)))))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f20,f15,f22,f22])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_tarski(sK0,sK1),k2_enumset1(sK2,sK3,sK4,sK5))),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_tarski(sK0,sK1),k2_enumset1(sK2,sK3,sK4,sK5))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f10,f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_tarski(sK0,sK1),k2_enumset1(sK2,sK3,sK4,sK5))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))),
% 0.21/0.47    inference(negated_conjecture,[],[f8])).
% 0.21/0.47  fof(f8,conjecture,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_enumset1)).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    spl6_2 | ~spl6_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f37,f32,f46])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)))),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)))),X3)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3))))) ) | ~spl6_1),
% 0.21/0.47    inference(superposition,[],[f33,f33])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    spl6_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f32])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (20184)------------------------------
% 0.21/0.47  % (20184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (20184)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (20184)Memory used [KB]: 7547
% 0.21/0.47  % (20184)Time elapsed: 0.037 s
% 0.21/0.47  % (20184)------------------------------
% 0.21/0.47  % (20184)------------------------------
% 0.21/0.48  % (20172)Success in time 0.114 s
%------------------------------------------------------------------------------
