%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:21 EST 2020

% Result     : Theorem 2.07s
% Output     : Refutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 544 expanded)
%              Number of leaves         :   15 ( 196 expanded)
%              Depth                    :   28
%              Number of atoms          :  120 ( 578 expanded)
%              Number of equality atoms :   85 ( 540 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3662,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f409,f3379])).

fof(f3379,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f3292])).

fof(f3292,plain,
    ( $false
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f408,f274])).

fof(f274,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),X3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,X3),X1),X2),X0)) = k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X4,X0)),X2)),X1)),X3)) ),
    inference(forward_demodulation,[],[f273,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),X0)) ),
    inference(forward_demodulation,[],[f40,f63])).

fof(f63,plain,(
    ! [X6,X4,X5] : k4_xboole_0(k4_xboole_0(X6,X4),k4_xboole_0(X5,X4)) = k4_xboole_0(k4_xboole_0(X6,X4),X5) ),
    inference(forward_demodulation,[],[f58,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f23,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f58,plain,(
    ! [X6,X4,X5] : k4_xboole_0(k4_xboole_0(X6,X4),k4_xboole_0(X5,X4)) = k4_xboole_0(X6,k5_xboole_0(X4,k4_xboole_0(X5,X4))) ),
    inference(superposition,[],[f38,f37])).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(definition_unfolding,[],[f21,f20,f20])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f25,f20,f20])).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f273,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),X3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,X3),X1),X2),X0)) = k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X4,X0)),X1),X2))),X3)) ),
    inference(forward_demodulation,[],[f272,f38])).

fof(f272,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),X3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,X3),X1),X2),X0)) = k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X4,X0)),k5_xboole_0(X1,k4_xboole_0(X2,X1))))),X3)) ),
    inference(forward_demodulation,[],[f271,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f271,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X4,X0)),k5_xboole_0(X1,k4_xboole_0(X2,X1)))),X3)) = k5_xboole_0(k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),X3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,X3),X1),X2),X0)) ),
    inference(forward_demodulation,[],[f270,f76])).

fof(f270,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X4,X0)),k5_xboole_0(X1,k4_xboole_0(X2,X1)))),X3)) = k5_xboole_0(k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2))),X3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,X3),X1),X2),X0)) ),
    inference(forward_demodulation,[],[f269,f22])).

fof(f269,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X4,X0)),k5_xboole_0(X1,k4_xboole_0(X2,X1)))),X3)) = k5_xboole_0(k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X2)),X3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,X3),X1),X2),X0)) ),
    inference(forward_demodulation,[],[f248,f38])).

fof(f248,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X4,X0)),k5_xboole_0(X1,k4_xboole_0(X2,X1)))),X3)) = k5_xboole_0(k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X2)),X3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,X3),k5_xboole_0(X1,k4_xboole_0(X2,X1))),X0)) ),
    inference(superposition,[],[f156,f38])).

fof(f156,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X0),X1),X2)) ),
    inference(forward_demodulation,[],[f155,f76])).

fof(f155,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X2,X0),X1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X0),X1),X2)) ),
    inference(forward_demodulation,[],[f154,f38])).

fof(f154,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0))))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X0),X1),X2)) ),
    inference(forward_demodulation,[],[f153,f22])).

fof(f153,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)),X0)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X0),X1),X2)) ),
    inference(forward_demodulation,[],[f152,f38])).

fof(f152,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)),X0)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),k4_xboole_0(k4_xboole_0(X3,k5_xboole_0(X0,k4_xboole_0(X1,X0))),X2)) ),
    inference(forward_demodulation,[],[f151,f38])).

fof(f151,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),k4_xboole_0(X3,k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)),X0)) ),
    inference(forward_demodulation,[],[f150,f76])).

fof(f150,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),k4_xboole_0(X3,k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k4_xboole_0(X3,X1),X2))),X0)) ),
    inference(forward_demodulation,[],[f149,f38])).

fof(f149,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),k4_xboole_0(X3,k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))))),X0)) ),
    inference(forward_demodulation,[],[f41,f22])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),k4_xboole_0(X3,k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))),X0)) ),
    inference(definition_unfolding,[],[f27,f20,f20,f20,f20,f20,f20])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_xboole_1)).

fof(f408,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f406])).

fof(f406,plain,
    ( spl8_2
  <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f409,plain,
    ( ~ spl8_2
    | spl8_1 ),
    inference(avatar_split_clause,[],[f404,f43,f406])).

fof(f43,plain,
    ( spl8_1
  <=> k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f404,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f403,f76])).

fof(f403,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK0)),k1_tarski(sK1)))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f402,f38])).

fof(f402,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f401,f22])).

fof(f401,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f400,f76])).

fof(f400,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4)),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK4)),k1_tarski(sK5)))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f399,f38])).

fof(f399,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4)),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4)))))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f398,f22])).

fof(f398,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f397,f38])).

fof(f397,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k1_tarski(sK2)),k1_tarski(sK3)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f396,f38])).

fof(f396,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))))
    | spl8_1 ),
    inference(forward_demodulation,[],[f395,f38])).

fof(f395,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f394,f76])).

fof(f394,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5)),k4_xboole_0(k4_xboole_0(k1_tarski(sK7),k1_tarski(sK5)),k1_tarski(sK6)))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f393,f38])).

fof(f393,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5)),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f392,f22])).

fof(f392,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f391,f76])).

fof(f391,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)),k4_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))))),k1_tarski(sK3)),k1_tarski(sK4)))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f390,f38])).

fof(f390,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f389,f76])).

fof(f389,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k4_xboole_0(k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))))))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f388,f38])).

fof(f388,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f387,f22])).

fof(f387,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))))))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f386,f22])).

fof(f386,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f385,f76])).

fof(f385,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k1_tarski(sK1)),k1_tarski(sK2)))),k1_tarski(sK0)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f384,f38])).

fof(f384,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))))),k1_tarski(sK0)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f383,f76])).

fof(f383,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k5_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k4_xboole_0(k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))))),k1_tarski(sK0)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f382,f38])).

fof(f382,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k5_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))))),k1_tarski(sK0)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f381,f22])).

fof(f381,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k5_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))))))),k1_tarski(sK0)))
    | spl8_1 ),
    inference(forward_demodulation,[],[f45,f22])).

fof(f45,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f46,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f36,f43])).

fof(f36,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))) ),
    inference(definition_unfolding,[],[f18,f33,f20,f35])).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))),k4_xboole_0(k1_tarski(X6),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))))) ),
    inference(definition_unfolding,[],[f29,f20,f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))) ),
    inference(definition_unfolding,[],[f28,f20,f31,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))) ),
    inference(definition_unfolding,[],[f26,f20,f31,f31])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f19,f20])).

fof(f19,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_enumset1)).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k4_xboole_0(k5_xboole_0(k1_tarski(X6),k4_xboole_0(k1_tarski(X7),k1_tarski(X6))),k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))))),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))))) ),
    inference(definition_unfolding,[],[f30,f20,f32,f32])).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(f18,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k1_tarski(sK0),k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k1_tarski(sK0),k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k1_tarski(sK0),k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:32:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (14870)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.45  % (14862)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (14867)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (14876)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (14869)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.47  % (14861)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (14868)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (14872)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (14875)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (14873)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (14864)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (14863)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (14877)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (14872)Refutation not found, incomplete strategy% (14872)------------------------------
% 0.21/0.49  % (14872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (14872)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (14872)Memory used [KB]: 10618
% 0.21/0.49  % (14872)Time elapsed: 0.081 s
% 0.21/0.49  % (14872)------------------------------
% 0.21/0.49  % (14872)------------------------------
% 0.21/0.49  % (14866)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (14874)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (14865)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (14871)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.52  % (14878)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 2.07/0.62  % (14867)Refutation found. Thanks to Tanya!
% 2.07/0.62  % SZS status Theorem for theBenchmark
% 2.07/0.62  % SZS output start Proof for theBenchmark
% 2.07/0.62  fof(f3662,plain,(
% 2.07/0.62    $false),
% 2.07/0.62    inference(avatar_sat_refutation,[],[f46,f409,f3379])).
% 2.07/0.62  fof(f3379,plain,(
% 2.07/0.62    spl8_2),
% 2.07/0.62    inference(avatar_contradiction_clause,[],[f3292])).
% 2.07/0.62  fof(f3292,plain,(
% 2.07/0.62    $false | spl8_2),
% 2.07/0.62    inference(unit_resulting_resolution,[],[f408,f274])).
% 2.07/0.62  fof(f274,plain,(
% 2.07/0.62    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),X3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,X3),X1),X2),X0)) = k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X4,X0)),X2)),X1)),X3))) )),
% 2.07/0.62    inference(forward_demodulation,[],[f273,f76])).
% 2.07/0.62  fof(f76,plain,(
% 2.07/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),X0))) )),
% 2.07/0.62    inference(forward_demodulation,[],[f40,f63])).
% 2.07/0.62  fof(f63,plain,(
% 2.07/0.62    ( ! [X6,X4,X5] : (k4_xboole_0(k4_xboole_0(X6,X4),k4_xboole_0(X5,X4)) = k4_xboole_0(k4_xboole_0(X6,X4),X5)) )),
% 2.07/0.62    inference(forward_demodulation,[],[f58,f38])).
% 2.07/0.62  fof(f38,plain,(
% 2.07/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 2.07/0.62    inference(definition_unfolding,[],[f23,f20])).
% 2.07/0.62  fof(f20,plain,(
% 2.07/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.07/0.62    inference(cnf_transformation,[],[f7])).
% 2.07/0.62  fof(f7,axiom,(
% 2.07/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.07/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.07/0.62  fof(f23,plain,(
% 2.07/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.07/0.62    inference(cnf_transformation,[],[f3])).
% 2.07/0.62  fof(f3,axiom,(
% 2.07/0.62    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.07/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.07/0.62  fof(f58,plain,(
% 2.07/0.62    ( ! [X6,X4,X5] : (k4_xboole_0(k4_xboole_0(X6,X4),k4_xboole_0(X5,X4)) = k4_xboole_0(X6,k5_xboole_0(X4,k4_xboole_0(X5,X4)))) )),
% 2.07/0.62    inference(superposition,[],[f38,f37])).
% 2.07/0.62  fof(f37,plain,(
% 2.07/0.62    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0))) )),
% 2.07/0.62    inference(definition_unfolding,[],[f21,f20,f20])).
% 2.07/0.62  fof(f21,plain,(
% 2.07/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.07/0.62    inference(cnf_transformation,[],[f2])).
% 2.07/0.62  fof(f2,axiom,(
% 2.07/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.07/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.07/0.62  fof(f40,plain,(
% 2.07/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2)))) )),
% 2.07/0.62    inference(definition_unfolding,[],[f25,f20,f20])).
% 2.07/0.62  fof(f25,plain,(
% 2.07/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 2.07/0.62    inference(cnf_transformation,[],[f4])).
% 2.07/0.62  fof(f4,axiom,(
% 2.07/0.62    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 2.07/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).
% 2.07/0.62  fof(f273,plain,(
% 2.07/0.62    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),X3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,X3),X1),X2),X0)) = k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X4,X0)),X1),X2))),X3))) )),
% 2.07/0.62    inference(forward_demodulation,[],[f272,f38])).
% 2.07/0.62  fof(f272,plain,(
% 2.07/0.62    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),X3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,X3),X1),X2),X0)) = k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X4,X0)),k5_xboole_0(X1,k4_xboole_0(X2,X1))))),X3))) )),
% 2.07/0.62    inference(forward_demodulation,[],[f271,f22])).
% 2.07/0.62  fof(f22,plain,(
% 2.07/0.62    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.07/0.62    inference(cnf_transformation,[],[f6])).
% 2.07/0.62  fof(f6,axiom,(
% 2.07/0.62    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.07/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.07/0.62  fof(f271,plain,(
% 2.07/0.62    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X4,X0)),k5_xboole_0(X1,k4_xboole_0(X2,X1)))),X3)) = k5_xboole_0(k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)),X3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,X3),X1),X2),X0))) )),
% 2.07/0.62    inference(forward_demodulation,[],[f270,f76])).
% 2.07/0.62  fof(f270,plain,(
% 2.07/0.62    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X4,X0)),k5_xboole_0(X1,k4_xboole_0(X2,X1)))),X3)) = k5_xboole_0(k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2))),X3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,X3),X1),X2),X0))) )),
% 2.07/0.62    inference(forward_demodulation,[],[f269,f22])).
% 2.07/0.62  fof(f269,plain,(
% 2.07/0.62    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X4,X0)),k5_xboole_0(X1,k4_xboole_0(X2,X1)))),X3)) = k5_xboole_0(k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X2)),X3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,X3),X1),X2),X0))) )),
% 2.07/0.62    inference(forward_demodulation,[],[f248,f38])).
% 2.07/0.62  fof(f248,plain,(
% 2.07/0.62    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X4,X0)),k5_xboole_0(X1,k4_xboole_0(X2,X1)))),X3)) = k5_xboole_0(k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X2)),X3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,X3),k5_xboole_0(X1,k4_xboole_0(X2,X1))),X0))) )),
% 2.07/0.62    inference(superposition,[],[f156,f38])).
% 2.07/0.62  fof(f156,plain,(
% 2.07/0.62    ( ! [X2,X0,X3,X1] : (k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X0),X1),X2))) )),
% 2.07/0.62    inference(forward_demodulation,[],[f155,f76])).
% 2.07/0.62  fof(f155,plain,(
% 2.07/0.62    ( ! [X2,X0,X3,X1] : (k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X2,X0),X1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X0),X1),X2))) )),
% 2.07/0.62    inference(forward_demodulation,[],[f154,f38])).
% 2.07/0.62  fof(f154,plain,(
% 2.07/0.62    ( ! [X2,X0,X3,X1] : (k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0))))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X0),X1),X2))) )),
% 2.07/0.62    inference(forward_demodulation,[],[f153,f22])).
% 2.07/0.62  fof(f153,plain,(
% 2.07/0.62    ( ! [X2,X0,X3,X1] : (k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)),X0)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X0),X1),X2))) )),
% 2.07/0.62    inference(forward_demodulation,[],[f152,f38])).
% 2.07/0.62  fof(f152,plain,(
% 2.07/0.62    ( ! [X2,X0,X3,X1] : (k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)),X0)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),k4_xboole_0(k4_xboole_0(X3,k5_xboole_0(X0,k4_xboole_0(X1,X0))),X2))) )),
% 2.07/0.62    inference(forward_demodulation,[],[f151,f38])).
% 2.07/0.62  fof(f151,plain,(
% 2.07/0.62    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),k4_xboole_0(X3,k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)),X0))) )),
% 2.07/0.62    inference(forward_demodulation,[],[f150,f76])).
% 2.07/0.62  fof(f150,plain,(
% 2.07/0.62    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),k4_xboole_0(X3,k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k4_xboole_0(X3,X1),X2))),X0))) )),
% 2.07/0.62    inference(forward_demodulation,[],[f149,f38])).
% 2.07/0.62  fof(f149,plain,(
% 2.07/0.62    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),k4_xboole_0(X3,k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))))),X0))) )),
% 2.07/0.62    inference(forward_demodulation,[],[f41,f22])).
% 2.07/0.62  fof(f41,plain,(
% 2.07/0.62    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),k4_xboole_0(X3,k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))),X0))) )),
% 2.07/0.62    inference(definition_unfolding,[],[f27,f20,f20,f20,f20,f20,f20])).
% 2.07/0.62  fof(f27,plain,(
% 2.07/0.62    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3))) )),
% 2.07/0.62    inference(cnf_transformation,[],[f1])).
% 2.07/0.62  fof(f1,axiom,(
% 2.07/0.62    ! [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3))),
% 2.07/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_xboole_1)).
% 2.07/0.62  fof(f408,plain,(
% 2.07/0.62    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3))) | spl8_2),
% 2.07/0.62    inference(avatar_component_clause,[],[f406])).
% 2.07/0.62  fof(f406,plain,(
% 2.07/0.62    spl8_2 <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)))),
% 2.07/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 2.07/0.62  fof(f409,plain,(
% 2.07/0.62    ~spl8_2 | spl8_1),
% 2.07/0.62    inference(avatar_split_clause,[],[f404,f43,f406])).
% 2.07/0.62  fof(f43,plain,(
% 2.07/0.62    spl8_1 <=> k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))),
% 2.07/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 2.07/0.62  fof(f404,plain,(
% 2.07/0.62    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3))) | spl8_1),
% 2.07/0.62    inference(forward_demodulation,[],[f403,f76])).
% 2.07/0.62  fof(f403,plain,(
% 2.07/0.62    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK0)),k1_tarski(sK1)))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3))) | spl8_1),
% 2.07/0.62    inference(forward_demodulation,[],[f402,f38])).
% 2.07/0.62  fof(f402,plain,(
% 2.07/0.62    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3))) | spl8_1),
% 2.07/0.62    inference(forward_demodulation,[],[f401,f22])).
% 2.07/0.62  fof(f401,plain,(
% 2.07/0.62    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3))) | spl8_1),
% 2.07/0.62    inference(forward_demodulation,[],[f400,f76])).
% 2.07/0.62  fof(f400,plain,(
% 2.07/0.62    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4)),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK4)),k1_tarski(sK5)))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3))) | spl8_1),
% 2.07/0.62    inference(forward_demodulation,[],[f399,f38])).
% 2.07/0.62  fof(f399,plain,(
% 2.07/0.62    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4)),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4)))))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3))) | spl8_1),
% 2.07/0.62    inference(forward_demodulation,[],[f398,f22])).
% 2.07/0.62  fof(f398,plain,(
% 2.07/0.62    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3))) | spl8_1),
% 2.07/0.62    inference(forward_demodulation,[],[f397,f38])).
% 2.07/0.62  fof(f397,plain,(
% 2.07/0.62    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k1_tarski(sK2)),k1_tarski(sK3))) | spl8_1),
% 2.07/0.62    inference(forward_demodulation,[],[f396,f38])).
% 2.07/0.62  fof(f396,plain,(
% 2.07/0.62    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))))) | spl8_1),
% 2.07/0.62    inference(forward_demodulation,[],[f395,f38])).
% 2.07/0.62  fof(f395,plain,(
% 2.07/0.62    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) | spl8_1),
% 2.07/0.62    inference(forward_demodulation,[],[f394,f76])).
% 2.07/0.62  fof(f394,plain,(
% 2.07/0.62    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5)),k4_xboole_0(k4_xboole_0(k1_tarski(sK7),k1_tarski(sK5)),k1_tarski(sK6)))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) | spl8_1),
% 2.07/0.62    inference(forward_demodulation,[],[f393,f38])).
% 2.07/0.62  fof(f393,plain,(
% 2.07/0.62    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5)),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) | spl8_1),
% 2.07/0.62    inference(forward_demodulation,[],[f392,f22])).
% 2.07/0.62  fof(f392,plain,(
% 2.07/0.62    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) | spl8_1),
% 2.07/0.62    inference(forward_demodulation,[],[f391,f76])).
% 2.07/0.62  fof(f391,plain,(
% 2.07/0.62    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)),k4_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))))),k1_tarski(sK3)),k1_tarski(sK4)))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) | spl8_1),
% 2.07/0.62    inference(forward_demodulation,[],[f390,f38])).
% 2.07/0.62  fof(f390,plain,(
% 2.07/0.62    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) | spl8_1),
% 2.07/0.62    inference(forward_demodulation,[],[f389,f76])).
% 2.07/0.62  fof(f389,plain,(
% 2.07/0.62    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k4_xboole_0(k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))))))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) | spl8_1),
% 2.07/0.62    inference(forward_demodulation,[],[f388,f38])).
% 2.07/0.62  fof(f388,plain,(
% 2.07/0.62    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) | spl8_1),
% 2.07/0.62    inference(forward_demodulation,[],[f387,f22])).
% 2.07/0.62  fof(f387,plain,(
% 2.07/0.62    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))))))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) | spl8_1),
% 2.07/0.62    inference(forward_demodulation,[],[f386,f22])).
% 2.07/0.62  fof(f386,plain,(
% 2.07/0.62    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) | spl8_1),
% 2.07/0.62    inference(forward_demodulation,[],[f385,f76])).
% 2.07/0.62  fof(f385,plain,(
% 2.07/0.62    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k1_tarski(sK1)),k1_tarski(sK2)))),k1_tarski(sK0))) | spl8_1),
% 2.07/0.62    inference(forward_demodulation,[],[f384,f38])).
% 2.07/0.62  fof(f384,plain,(
% 2.07/0.62    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))))),k1_tarski(sK0))) | spl8_1),
% 2.07/0.62    inference(forward_demodulation,[],[f383,f76])).
% 2.07/0.62  fof(f383,plain,(
% 2.07/0.62    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k5_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k4_xboole_0(k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))))),k1_tarski(sK0))) | spl8_1),
% 2.07/0.62    inference(forward_demodulation,[],[f382,f38])).
% 2.07/0.62  fof(f382,plain,(
% 2.07/0.62    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k5_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))))),k1_tarski(sK0))) | spl8_1),
% 2.07/0.62    inference(forward_demodulation,[],[f381,f22])).
% 2.07/0.62  fof(f381,plain,(
% 2.07/0.62    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k5_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))))))),k1_tarski(sK0))) | spl8_1),
% 2.07/0.62    inference(forward_demodulation,[],[f45,f22])).
% 2.07/0.62  fof(f45,plain,(
% 2.07/0.62    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))) | spl8_1),
% 2.07/0.62    inference(avatar_component_clause,[],[f43])).
% 2.07/0.62  fof(f46,plain,(
% 2.07/0.62    ~spl8_1),
% 2.07/0.62    inference(avatar_split_clause,[],[f36,f43])).
% 2.07/0.62  fof(f36,plain,(
% 2.07/0.62    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_tarski(sK7),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))),
% 2.07/0.62    inference(definition_unfolding,[],[f18,f33,f20,f35])).
% 2.07/0.62  fof(f35,plain,(
% 2.07/0.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))),k4_xboole_0(k1_tarski(X6),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))))))) )),
% 2.07/0.62    inference(definition_unfolding,[],[f29,f20,f34])).
% 2.07/0.62  fof(f34,plain,(
% 2.07/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))))) )),
% 2.07/0.62    inference(definition_unfolding,[],[f28,f20,f31,f32])).
% 2.07/0.62  fof(f32,plain,(
% 2.07/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))))) )),
% 2.07/0.62    inference(definition_unfolding,[],[f26,f20,f31,f31])).
% 2.07/0.62  fof(f26,plain,(
% 2.07/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 2.07/0.62    inference(cnf_transformation,[],[f8])).
% 2.07/0.62  fof(f8,axiom,(
% 2.07/0.62    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 2.07/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 2.07/0.62  fof(f31,plain,(
% 2.07/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))) )),
% 2.07/0.62    inference(definition_unfolding,[],[f19,f20])).
% 2.07/0.62  fof(f19,plain,(
% 2.07/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 2.07/0.62    inference(cnf_transformation,[],[f10])).
% 2.07/0.62  fof(f10,axiom,(
% 2.07/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 2.07/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 2.07/0.62  fof(f28,plain,(
% 2.07/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))) )),
% 2.07/0.62    inference(cnf_transformation,[],[f11])).
% 2.07/0.62  fof(f11,axiom,(
% 2.07/0.62    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))),
% 2.07/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_enumset1)).
% 2.07/0.62  fof(f29,plain,(
% 2.07/0.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 2.07/0.62    inference(cnf_transformation,[],[f12])).
% 2.07/0.62  fof(f12,axiom,(
% 2.07/0.62    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 2.07/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).
% 2.07/0.62  fof(f33,plain,(
% 2.07/0.62    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k4_xboole_0(k5_xboole_0(k1_tarski(X6),k4_xboole_0(k1_tarski(X7),k1_tarski(X6))),k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))))),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))))))) )),
% 2.07/0.62    inference(definition_unfolding,[],[f30,f20,f32,f32])).
% 2.07/0.62  fof(f30,plain,(
% 2.07/0.62    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 2.07/0.62    inference(cnf_transformation,[],[f9])).
% 2.07/0.62  fof(f9,axiom,(
% 2.07/0.62    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 2.07/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).
% 2.07/0.62  fof(f18,plain,(
% 2.07/0.62    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k1_tarski(sK0),k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7))),
% 2.07/0.62    inference(cnf_transformation,[],[f17])).
% 2.07/0.62  fof(f17,plain,(
% 2.07/0.62    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k1_tarski(sK0),k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7))),
% 2.07/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f15,f16])).
% 2.07/0.62  fof(f16,plain,(
% 2.07/0.62    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k1_tarski(sK0),k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7))),
% 2.07/0.62    introduced(choice_axiom,[])).
% 2.07/0.62  fof(f15,plain,(
% 2.07/0.62    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))),
% 2.07/0.62    inference(ennf_transformation,[],[f14])).
% 2.07/0.62  fof(f14,negated_conjecture,(
% 2.07/0.62    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))),
% 2.07/0.62    inference(negated_conjecture,[],[f13])).
% 2.07/0.62  fof(f13,conjecture,(
% 2.07/0.62    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))),
% 2.07/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).
% 2.07/0.62  % SZS output end Proof for theBenchmark
% 2.07/0.62  % (14867)------------------------------
% 2.07/0.62  % (14867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.62  % (14867)Termination reason: Refutation
% 2.07/0.62  
% 2.07/0.62  % (14867)Memory used [KB]: 10490
% 2.07/0.62  % (14867)Time elapsed: 0.171 s
% 2.07/0.62  % (14867)------------------------------
% 2.07/0.62  % (14867)------------------------------
% 2.07/0.62  % (14860)Success in time 0.263 s
%------------------------------------------------------------------------------
