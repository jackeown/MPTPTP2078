%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 197 expanded)
%              Number of leaves         :   13 (  75 expanded)
%              Depth                    :   12
%              Number of atoms          :   63 ( 224 expanded)
%              Number of equality atoms :   42 ( 192 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f46,f50,f136])).

fof(f136,plain,
    ( ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f32,f90])).

fof(f90,plain,
    ( ! [X21,X19,X17,X22,X20,X18] : k5_xboole_0(k5_xboole_0(X17,k5_xboole_0(k5_xboole_0(X18,k5_xboole_0(X19,k3_xboole_0(X19,X18))),k3_xboole_0(k5_xboole_0(X18,k5_xboole_0(X19,k3_xboole_0(X19,X18))),X17))),k5_xboole_0(k5_xboole_0(k5_xboole_0(X20,k5_xboole_0(X21,k3_xboole_0(X21,X20))),k5_xboole_0(X22,k3_xboole_0(X22,k5_xboole_0(X20,k5_xboole_0(X21,k3_xboole_0(X21,X20)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X20,k5_xboole_0(X21,k3_xboole_0(X21,X20))),k5_xboole_0(X22,k3_xboole_0(X22,k5_xboole_0(X20,k5_xboole_0(X21,k3_xboole_0(X21,X20)))))),k5_xboole_0(X17,k5_xboole_0(k5_xboole_0(X18,k5_xboole_0(X19,k3_xboole_0(X19,X18))),k3_xboole_0(k5_xboole_0(X18,k5_xboole_0(X19,k3_xboole_0(X19,X18))),X17)))))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X17,k5_xboole_0(X18,k3_xboole_0(X18,X17))),k5_xboole_0(k5_xboole_0(X19,k5_xboole_0(X20,k3_xboole_0(X20,X19))),k3_xboole_0(k5_xboole_0(X19,k5_xboole_0(X20,k3_xboole_0(X20,X19))),k5_xboole_0(X17,k5_xboole_0(X18,k3_xboole_0(X18,X17)))))),k5_xboole_0(k5_xboole_0(X21,k5_xboole_0(X22,k3_xboole_0(X22,X21))),k3_xboole_0(k5_xboole_0(X21,k5_xboole_0(X22,k3_xboole_0(X22,X21))),k5_xboole_0(k5_xboole_0(X17,k5_xboole_0(X18,k3_xboole_0(X18,X17))),k5_xboole_0(k5_xboole_0(X19,k5_xboole_0(X20,k3_xboole_0(X20,X19))),k3_xboole_0(k5_xboole_0(X19,k5_xboole_0(X20,k3_xboole_0(X20,X19))),k5_xboole_0(X17,k5_xboole_0(X18,k3_xboole_0(X18,X17)))))))))
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(superposition,[],[f49,f45])).

fof(f45,plain,
    ( ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))))))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl7_2
  <=> ! [X1,X3,X0,X2] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f49,plain,
    ( ! [X6,X4,X7,X5] : k5_xboole_0(k5_xboole_0(X7,k5_xboole_0(X4,k3_xboole_0(X4,X7))),k5_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),k3_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),k5_xboole_0(X7,k5_xboole_0(X4,k3_xboole_0(X4,X7)))))) = k5_xboole_0(X7,k5_xboole_0(k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))),k5_xboole_0(X6,k3_xboole_0(X6,k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))),k5_xboole_0(X6,k3_xboole_0(X6,k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4)))))),X7)))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl7_3
  <=> ! [X5,X7,X4,X6] : k5_xboole_0(k5_xboole_0(X7,k5_xboole_0(X4,k3_xboole_0(X4,X7))),k5_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),k3_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),k5_xboole_0(X7,k5_xboole_0(X4,k3_xboole_0(X4,X7)))))) = k5_xboole_0(X7,k5_xboole_0(k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))),k5_xboole_0(X6,k3_xboole_0(X6,k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))),k5_xboole_0(X6,k3_xboole_0(X6,k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4)))))),X7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f32,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK0))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))))))) ),
    inference(forward_demodulation,[],[f31,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))) ),
    inference(definition_unfolding,[],[f19,f23,f23,f23,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f17,f15])).

fof(f15,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f31,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0))))))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK0))))))) ),
    inference(backward_demodulation,[],[f29,f30])).

fof(f29,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK0))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK0)))))))))) ),
    inference(definition_unfolding,[],[f14,f28,f23,f26,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))) ),
    inference(definition_unfolding,[],[f16,f23])).

fof(f16,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k1_tarski(X0)))),k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k1_tarski(X0))))))) ),
    inference(definition_unfolding,[],[f21,f23,f25,f24])).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k1_tarski(X0)))) ),
    inference(definition_unfolding,[],[f18,f23,f24])).

fof(f18,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))),k1_tarski(X0)))),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k1_tarski(X4)))),k3_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k1_tarski(X4)))),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))),k1_tarski(X0))))))) ),
    inference(definition_unfolding,[],[f22,f23,f27,f25])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))),k1_tarski(X0)))) ),
    inference(definition_unfolding,[],[f20,f23,f25])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f22,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).

fof(f14,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

fof(f50,plain,
    ( spl7_3
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f41,f34,f48])).

fof(f34,plain,
    ( spl7_1
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f41,plain,
    ( ! [X6,X4,X7,X5] : k5_xboole_0(k5_xboole_0(X7,k5_xboole_0(X4,k3_xboole_0(X4,X7))),k5_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),k3_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),k5_xboole_0(X7,k5_xboole_0(X4,k3_xboole_0(X4,X7)))))) = k5_xboole_0(X7,k5_xboole_0(k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))),k5_xboole_0(X6,k3_xboole_0(X6,k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))),k5_xboole_0(X6,k3_xboole_0(X6,k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4)))))),X7)))
    | ~ spl7_1 ),
    inference(superposition,[],[f35,f35])).

fof(f35,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0)))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f46,plain,
    ( spl7_2
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f37,f34,f44])).

fof(f37,plain,
    ( ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))))))
    | ~ spl7_1 ),
    inference(superposition,[],[f35,f35])).

fof(f36,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f30,f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:57:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (10040)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (10036)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (10040)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f36,f46,f50,f136])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    ~spl7_2 | ~spl7_3),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f135])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    $false | (~spl7_2 | ~spl7_3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f32,f90])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ( ! [X21,X19,X17,X22,X20,X18] : (k5_xboole_0(k5_xboole_0(X17,k5_xboole_0(k5_xboole_0(X18,k5_xboole_0(X19,k3_xboole_0(X19,X18))),k3_xboole_0(k5_xboole_0(X18,k5_xboole_0(X19,k3_xboole_0(X19,X18))),X17))),k5_xboole_0(k5_xboole_0(k5_xboole_0(X20,k5_xboole_0(X21,k3_xboole_0(X21,X20))),k5_xboole_0(X22,k3_xboole_0(X22,k5_xboole_0(X20,k5_xboole_0(X21,k3_xboole_0(X21,X20)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X20,k5_xboole_0(X21,k3_xboole_0(X21,X20))),k5_xboole_0(X22,k3_xboole_0(X22,k5_xboole_0(X20,k5_xboole_0(X21,k3_xboole_0(X21,X20)))))),k5_xboole_0(X17,k5_xboole_0(k5_xboole_0(X18,k5_xboole_0(X19,k3_xboole_0(X19,X18))),k3_xboole_0(k5_xboole_0(X18,k5_xboole_0(X19,k3_xboole_0(X19,X18))),X17)))))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X17,k5_xboole_0(X18,k3_xboole_0(X18,X17))),k5_xboole_0(k5_xboole_0(X19,k5_xboole_0(X20,k3_xboole_0(X20,X19))),k3_xboole_0(k5_xboole_0(X19,k5_xboole_0(X20,k3_xboole_0(X20,X19))),k5_xboole_0(X17,k5_xboole_0(X18,k3_xboole_0(X18,X17)))))),k5_xboole_0(k5_xboole_0(X21,k5_xboole_0(X22,k3_xboole_0(X22,X21))),k3_xboole_0(k5_xboole_0(X21,k5_xboole_0(X22,k3_xboole_0(X22,X21))),k5_xboole_0(k5_xboole_0(X17,k5_xboole_0(X18,k3_xboole_0(X18,X17))),k5_xboole_0(k5_xboole_0(X19,k5_xboole_0(X20,k3_xboole_0(X20,X19))),k3_xboole_0(k5_xboole_0(X19,k5_xboole_0(X20,k3_xboole_0(X20,X19))),k5_xboole_0(X17,k5_xboole_0(X18,k3_xboole_0(X18,X17)))))))))) ) | (~spl7_2 | ~spl7_3)),
% 0.21/0.50    inference(superposition,[],[f49,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))))))) ) | ~spl7_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    spl7_2 <=> ! [X1,X3,X0,X2] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X6,X4,X7,X5] : (k5_xboole_0(k5_xboole_0(X7,k5_xboole_0(X4,k3_xboole_0(X4,X7))),k5_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),k3_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),k5_xboole_0(X7,k5_xboole_0(X4,k3_xboole_0(X4,X7)))))) = k5_xboole_0(X7,k5_xboole_0(k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))),k5_xboole_0(X6,k3_xboole_0(X6,k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))),k5_xboole_0(X6,k3_xboole_0(X6,k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4)))))),X7)))) ) | ~spl7_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    spl7_3 <=> ! [X5,X7,X4,X6] : k5_xboole_0(k5_xboole_0(X7,k5_xboole_0(X4,k3_xboole_0(X4,X7))),k5_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),k3_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),k5_xboole_0(X7,k5_xboole_0(X4,k3_xboole_0(X4,X7)))))) = k5_xboole_0(X7,k5_xboole_0(k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))),k5_xboole_0(X6,k3_xboole_0(X6,k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))),k5_xboole_0(X6,k3_xboole_0(X6,k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4)))))),X7)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK0))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))))))),
% 0.21/0.50    inference(forward_demodulation,[],[f31,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f19,f23,f23,f23,f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f17,f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0))))))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK0)))))))),
% 0.21/0.50    inference(backward_demodulation,[],[f29,f30])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK0))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK0))))))))))),
% 0.21/0.50    inference(definition_unfolding,[],[f14,f28,f23,f26,f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0))))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f16,f23])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k1_tarski(X0)))),k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k1_tarski(X0)))))))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f21,f23,f25,f24])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k1_tarski(X0))))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f18,f23,f24])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))),k1_tarski(X0)))),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k1_tarski(X4)))),k3_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k1_tarski(X4)))),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))),k1_tarski(X0)))))))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f22,f23,f27,f25])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))),k1_tarski(X0))))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f20,f23,f25])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f11,f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.21/0.50    inference(negated_conjecture,[],[f9])).
% 0.21/0.50  fof(f9,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    spl7_3 | ~spl7_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f41,f34,f48])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    spl7_1 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X6,X4,X7,X5] : (k5_xboole_0(k5_xboole_0(X7,k5_xboole_0(X4,k3_xboole_0(X4,X7))),k5_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),k3_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),k5_xboole_0(X7,k5_xboole_0(X4,k3_xboole_0(X4,X7)))))) = k5_xboole_0(X7,k5_xboole_0(k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))),k5_xboole_0(X6,k3_xboole_0(X6,k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))),k5_xboole_0(X6,k3_xboole_0(X6,k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4)))))),X7)))) ) | ~spl7_1),
% 0.21/0.50    inference(superposition,[],[f35,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0)))) ) | ~spl7_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f34])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    spl7_2 | ~spl7_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f37,f34,f44])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))))))) ) | ~spl7_1),
% 0.21/0.50    inference(superposition,[],[f35,f35])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    spl7_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f30,f34])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (10040)------------------------------
% 0.21/0.50  % (10040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (10040)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (10040)Memory used [KB]: 7675
% 0.21/0.50  % (10040)Time elapsed: 0.067 s
% 0.21/0.50  % (10040)------------------------------
% 0.21/0.50  % (10040)------------------------------
% 0.21/0.50  % (10032)Success in time 0.144 s
%------------------------------------------------------------------------------
