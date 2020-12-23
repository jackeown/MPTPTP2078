%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 219 expanded)
%              Number of leaves         :   12 (  85 expanded)
%              Depth                    :   15
%              Number of atoms          :   67 ( 233 expanded)
%              Number of equality atoms :   51 ( 216 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f67])).

fof(f67,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | spl8_1 ),
    inference(trivial_inequality_removal,[],[f65])).

fof(f65,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f64,f39])).

fof(f39,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(k4_xboole_0(X4,X3),k4_xboole_0(X5,k5_xboole_0(X3,k4_xboole_0(X4,X3))))) = k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),X3)) ),
    inference(superposition,[],[f32,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f32,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
    inference(definition_unfolding,[],[f20,f17,f17,f17,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f20,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f64,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4)),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4)))))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f63,f19])).

fof(f63,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f62,f39])).

fof(f62,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3)),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3)))))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f61,f19])).

fof(f61,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f60,f39])).

fof(f60,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2)),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f59,f19])).

fof(f59,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f58,f39])).

fof(f58,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1)),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1)))))),k1_tarski(sK0)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f56,f19])).

fof(f56,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl8_1 ),
    inference(superposition,[],[f54,f32])).

fof(f54,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl8_1
  <=> k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f55,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f49,f52])).

fof(f49,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f48,f39])).

fof(f48,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2)),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f47,f19])).

fof(f47,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f46,f39])).

fof(f46,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1)),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1)))))),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f45,f19])).

fof(f45,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))))),k1_tarski(sK0))) ),
    inference(backward_demodulation,[],[f33,f39])).

fof(f33,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))))) ),
    inference(backward_demodulation,[],[f31,f19])).

fof(f31,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) ),
    inference(definition_unfolding,[],[f15,f28,f17,f30,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f16,f17])).

fof(f16,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f23,f17,f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f22,f17,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f21,f17,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f18,f17,f25])).

fof(f18,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k5_xboole_0(k1_tarski(X6),k4_xboole_0(k1_tarski(X7),k1_tarski(X6))),k1_tarski(X5))),k1_tarski(X4))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))))) ),
    inference(definition_unfolding,[],[f24,f17,f27,f27])).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(f15,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:38:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.44  % (8658)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.44  % (8658)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.45  % (8650)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f68,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f55,f67])).
% 0.22/0.45  fof(f67,plain,(
% 0.22/0.45    spl8_1),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f66])).
% 0.22/0.45  fof(f66,plain,(
% 0.22/0.45    $false | spl8_1),
% 0.22/0.45    inference(trivial_inequality_removal,[],[f65])).
% 0.22/0.45  fof(f65,plain,(
% 0.22/0.45    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) | spl8_1),
% 0.22/0.45    inference(forward_demodulation,[],[f64,f39])).
% 0.22/0.45  fof(f39,plain,(
% 0.22/0.45    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(k4_xboole_0(X4,X3),k4_xboole_0(X5,k5_xboole_0(X3,k4_xboole_0(X4,X3))))) = k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),X3))) )),
% 0.22/0.45    inference(superposition,[],[f32,f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0))) )),
% 0.22/0.45    inference(definition_unfolding,[],[f20,f17,f17,f17,f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.45  fof(f64,plain,(
% 0.22/0.45    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4)),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4)))))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) | spl8_1),
% 0.22/0.45    inference(forward_demodulation,[],[f63,f19])).
% 0.22/0.45  fof(f63,plain,(
% 0.22/0.45    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) | spl8_1),
% 0.22/0.45    inference(forward_demodulation,[],[f62,f39])).
% 0.22/0.45  fof(f62,plain,(
% 0.22/0.45    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3)),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3)))))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) | spl8_1),
% 0.22/0.45    inference(forward_demodulation,[],[f61,f19])).
% 0.22/0.45  fof(f61,plain,(
% 0.22/0.45    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) | spl8_1),
% 0.22/0.45    inference(forward_demodulation,[],[f60,f39])).
% 0.22/0.45  fof(f60,plain,(
% 0.22/0.45    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2)),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK1))),k1_tarski(sK0))) | spl8_1),
% 0.22/0.45    inference(forward_demodulation,[],[f59,f19])).
% 0.22/0.45  fof(f59,plain,(
% 0.22/0.45    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))))),k1_tarski(sK1))),k1_tarski(sK0))) | spl8_1),
% 0.22/0.45    inference(forward_demodulation,[],[f58,f39])).
% 0.22/0.45  fof(f58,plain,(
% 0.22/0.45    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1)),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1)))))),k1_tarski(sK0))) | spl8_1),
% 0.22/0.45    inference(forward_demodulation,[],[f56,f19])).
% 0.22/0.45  fof(f56,plain,(
% 0.22/0.45    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) | spl8_1),
% 0.22/0.45    inference(superposition,[],[f54,f32])).
% 0.22/0.45  fof(f54,plain,(
% 0.22/0.45    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) | spl8_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f52])).
% 0.22/0.45  fof(f52,plain,(
% 0.22/0.45    spl8_1 <=> k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.45  fof(f55,plain,(
% 0.22/0.45    ~spl8_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f49,f52])).
% 0.22/0.45  fof(f49,plain,(
% 0.22/0.45    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))),
% 0.22/0.45    inference(forward_demodulation,[],[f48,f39])).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2)),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))))),k1_tarski(sK1))),k1_tarski(sK0)))),
% 0.22/0.45    inference(forward_demodulation,[],[f47,f19])).
% 0.22/0.45  fof(f47,plain,(
% 0.22/0.45    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))))),k1_tarski(sK1))),k1_tarski(sK0)))),
% 0.22/0.45    inference(forward_demodulation,[],[f46,f39])).
% 0.22/0.45  fof(f46,plain,(
% 0.22/0.45    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1)),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1)))))),k1_tarski(sK0)))),
% 0.22/0.45    inference(forward_demodulation,[],[f45,f19])).
% 0.22/0.45  fof(f45,plain,(
% 0.22/0.45    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))))),k1_tarski(sK0)))),
% 0.22/0.45    inference(backward_demodulation,[],[f33,f39])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))))),
% 0.22/0.45    inference(backward_demodulation,[],[f31,f19])).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))))),
% 0.22/0.45    inference(definition_unfolding,[],[f15,f28,f17,f30,f25])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))) )),
% 0.22/0.45    inference(definition_unfolding,[],[f16,f17])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.22/0.45    inference(definition_unfolding,[],[f23,f17,f29])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.22/0.45    inference(definition_unfolding,[],[f22,f17,f27])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.22/0.45    inference(definition_unfolding,[],[f21,f17,f26])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.22/0.45    inference(definition_unfolding,[],[f18,f17,f25])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,axiom,(
% 0.22/0.45    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f8])).
% 0.22/0.45  fof(f8,axiom,(
% 0.22/0.45    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,axiom,(
% 0.22/0.45    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k5_xboole_0(k1_tarski(X6),k4_xboole_0(k1_tarski(X7),k1_tarski(X6))),k1_tarski(X5))),k1_tarski(X4))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0)))))) )),
% 0.22/0.45    inference(definition_unfolding,[],[f24,f17,f27,f27])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7))),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f12,f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.22/0.45    inference(ennf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.22/0.45    inference(negated_conjecture,[],[f10])).
% 0.22/0.45  fof(f10,conjecture,(
% 0.22/0.45    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (8658)------------------------------
% 0.22/0.45  % (8658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (8658)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (8658)Memory used [KB]: 10746
% 0.22/0.45  % (8658)Time elapsed: 0.052 s
% 0.22/0.45  % (8658)------------------------------
% 0.22/0.45  % (8658)------------------------------
% 0.22/0.46  % (8642)Success in time 0.099 s
%------------------------------------------------------------------------------
