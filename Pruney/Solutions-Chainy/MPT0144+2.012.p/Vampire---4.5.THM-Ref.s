%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 226 expanded)
%              Number of leaves         :   11 (  84 expanded)
%              Depth                    :    9
%              Number of atoms          :   44 ( 232 expanded)
%              Number of equality atoms :   36 ( 223 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f74])).

fof(f74,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | spl7_1 ),
    inference(subsumption_resolution,[],[f72,f38])).

fof(f38,plain,(
    ! [X6,X10,X8,X7,X5,X9] : k5_xboole_0(k5_xboole_0(X9,k5_xboole_0(k5_xboole_0(X10,k5_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),k3_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),X10))),k3_xboole_0(k5_xboole_0(X10,k5_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),k3_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),X10))),X9))),k5_xboole_0(k5_xboole_0(X7,k5_xboole_0(X8,k3_xboole_0(X8,X7))),k3_xboole_0(k5_xboole_0(X7,k5_xboole_0(X8,k3_xboole_0(X8,X7))),k5_xboole_0(X9,k5_xboole_0(k5_xboole_0(X10,k5_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),k3_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),X10))),k3_xboole_0(k5_xboole_0(X10,k5_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),k3_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),X10))),X9)))))) = k5_xboole_0(k5_xboole_0(X9,k5_xboole_0(X10,k3_xboole_0(X10,X9))),k5_xboole_0(k5_xboole_0(k5_xboole_0(X5,k5_xboole_0(k5_xboole_0(X6,k5_xboole_0(X7,k3_xboole_0(X7,X6))),k3_xboole_0(k5_xboole_0(X6,k5_xboole_0(X7,k3_xboole_0(X7,X6))),X5))),k5_xboole_0(X8,k3_xboole_0(X8,k5_xboole_0(X5,k5_xboole_0(k5_xboole_0(X6,k5_xboole_0(X7,k3_xboole_0(X7,X6))),k3_xboole_0(k5_xboole_0(X6,k5_xboole_0(X7,k3_xboole_0(X7,X6))),X5)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X5,k5_xboole_0(k5_xboole_0(X6,k5_xboole_0(X7,k3_xboole_0(X7,X6))),k3_xboole_0(k5_xboole_0(X6,k5_xboole_0(X7,k3_xboole_0(X7,X6))),X5))),k5_xboole_0(X8,k3_xboole_0(X8,k5_xboole_0(X5,k5_xboole_0(k5_xboole_0(X6,k5_xboole_0(X7,k3_xboole_0(X7,X6))),k3_xboole_0(k5_xboole_0(X6,k5_xboole_0(X7,k3_xboole_0(X7,X6))),X5)))))),k5_xboole_0(X9,k5_xboole_0(X10,k3_xboole_0(X10,X9)))))) ),
    inference(superposition,[],[f31,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0)))))) ),
    inference(superposition,[],[f30,f30])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f72,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0))))))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2))))))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))))
    | spl7_1 ),
    inference(forward_demodulation,[],[f70,f30])).

fof(f70,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))))))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl7_1
  <=> k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0))))))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f71,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f29,f68])).

fof(f29,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))))))) ),
    inference(definition_unfolding,[],[f14,f27,f23,f28,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))) ),
    inference(definition_unfolding,[],[f16,f23])).

fof(f16,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k1_tarski(X2)))),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0))))))) ),
    inference(definition_unfolding,[],[f21,f23,f24,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k1_tarski(X0)))) ),
    inference(definition_unfolding,[],[f18,f23,f24])).

fof(f18,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))),k1_tarski(X0)))),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k1_tarski(X4)))),k3_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k1_tarski(X4)))),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))),k1_tarski(X0))))))) ),
    inference(definition_unfolding,[],[f22,f23,f26,f25])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))),k1_tarski(X0)))) ),
    inference(definition_unfolding,[],[f20,f23,f25])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f22,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (8622)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.44  % (8622)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f71,f74])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    spl7_1),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f73])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    $false | spl7_1),
% 0.21/0.44    inference(subsumption_resolution,[],[f72,f38])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ( ! [X6,X10,X8,X7,X5,X9] : (k5_xboole_0(k5_xboole_0(X9,k5_xboole_0(k5_xboole_0(X10,k5_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),k3_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),X10))),k3_xboole_0(k5_xboole_0(X10,k5_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),k3_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),X10))),X9))),k5_xboole_0(k5_xboole_0(X7,k5_xboole_0(X8,k3_xboole_0(X8,X7))),k3_xboole_0(k5_xboole_0(X7,k5_xboole_0(X8,k3_xboole_0(X8,X7))),k5_xboole_0(X9,k5_xboole_0(k5_xboole_0(X10,k5_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),k3_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),X10))),k3_xboole_0(k5_xboole_0(X10,k5_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),k3_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))),X10))),X9)))))) = k5_xboole_0(k5_xboole_0(X9,k5_xboole_0(X10,k3_xboole_0(X10,X9))),k5_xboole_0(k5_xboole_0(k5_xboole_0(X5,k5_xboole_0(k5_xboole_0(X6,k5_xboole_0(X7,k3_xboole_0(X7,X6))),k3_xboole_0(k5_xboole_0(X6,k5_xboole_0(X7,k3_xboole_0(X7,X6))),X5))),k5_xboole_0(X8,k3_xboole_0(X8,k5_xboole_0(X5,k5_xboole_0(k5_xboole_0(X6,k5_xboole_0(X7,k3_xboole_0(X7,X6))),k3_xboole_0(k5_xboole_0(X6,k5_xboole_0(X7,k3_xboole_0(X7,X6))),X5)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X5,k5_xboole_0(k5_xboole_0(X6,k5_xboole_0(X7,k3_xboole_0(X7,X6))),k3_xboole_0(k5_xboole_0(X6,k5_xboole_0(X7,k3_xboole_0(X7,X6))),X5))),k5_xboole_0(X8,k3_xboole_0(X8,k5_xboole_0(X5,k5_xboole_0(k5_xboole_0(X6,k5_xboole_0(X7,k3_xboole_0(X7,X6))),k3_xboole_0(k5_xboole_0(X6,k5_xboole_0(X7,k3_xboole_0(X7,X6))),X5)))))),k5_xboole_0(X9,k5_xboole_0(X10,k3_xboole_0(X10,X9))))))) )),
% 0.21/0.44    inference(superposition,[],[f31,f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))))))) )),
% 0.21/0.44    inference(superposition,[],[f30,f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0)))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f19,f23,f23,f23,f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f17,f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0))))))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2))))))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) | spl7_1),
% 0.21/0.44    inference(forward_demodulation,[],[f70,f30])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))))))) | spl7_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f68])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    spl7_1 <=> k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0))))))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    ~spl7_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f29,f68])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k1_tarski(sK4)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))))))),
% 0.21/0.44    inference(definition_unfolding,[],[f14,f27,f23,f28,f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0))))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f16,f23])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k1_tarski(X2)))),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))))))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f21,f23,f24,f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k1_tarski(X0))))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f18,f23,f24])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))),k1_tarski(X0)))),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k1_tarski(X4)))),k3_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k1_tarski(X4)))),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))),k1_tarski(X0)))))))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f22,f23,f26,f25])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))),k1_tarski(X0))))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f20,f23,f25])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f11,f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.21/0.44    inference(ennf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.21/0.44    inference(negated_conjecture,[],[f9])).
% 0.21/0.44  fof(f9,conjecture,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (8622)------------------------------
% 0.21/0.44  % (8622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (8622)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (8622)Memory used [KB]: 11385
% 0.21/0.44  % (8622)Time elapsed: 0.042 s
% 0.21/0.44  % (8622)------------------------------
% 0.21/0.44  % (8622)------------------------------
% 0.21/0.44  % (8605)Success in time 0.084 s
%------------------------------------------------------------------------------
