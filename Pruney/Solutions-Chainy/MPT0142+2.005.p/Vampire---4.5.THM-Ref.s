%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 172 expanded)
%              Number of leaves         :   11 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :   37 ( 173 expanded)
%              Number of equality atoms :   36 ( 172 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :   17 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f42,plain,(
    $false ),
    inference(subsumption_resolution,[],[f41,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))) ),
    inference(definition_unfolding,[],[f20,f25,f25,f25,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f18,f16])).

fof(f16,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f20,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f41,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) ),
    inference(forward_demodulation,[],[f40,f33])).

fof(f40,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK0))))))) ),
    inference(forward_demodulation,[],[f32,f33])).

fof(f32,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0)))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))))))) ),
    inference(definition_unfolding,[],[f15,f31,f25,f28,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0))))))) ),
    inference(definition_unfolding,[],[f21,f25,f26,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))) ),
    inference(definition_unfolding,[],[f17,f25])).

fof(f17,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f28,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0))))))) ),
    inference(definition_unfolding,[],[f19,f25,f26])).

fof(f19,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3))))))),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3))))))),k1_tarski(X2)))),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3))))))),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3))))))),k1_tarski(X2)))),k1_tarski(X1)))),k1_tarski(X0)))) ),
    inference(definition_unfolding,[],[f24,f25,f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k1_tarski(X5),k3_xboole_0(k1_tarski(X5),k1_tarski(X4)))),k3_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k1_tarski(X5),k3_xboole_0(k1_tarski(X5),k1_tarski(X4)))),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k1_tarski(X5),k3_xboole_0(k1_tarski(X5),k1_tarski(X4)))),k3_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k1_tarski(X5),k3_xboole_0(k1_tarski(X5),k1_tarski(X4)))),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2))))))),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k1_tarski(X5),k3_xboole_0(k1_tarski(X5),k1_tarski(X4)))),k3_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k1_tarski(X5),k3_xboole_0(k1_tarski(X5),k1_tarski(X4)))),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k1_tarski(X5),k3_xboole_0(k1_tarski(X5),k1_tarski(X4)))),k3_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k1_tarski(X5),k3_xboole_0(k1_tarski(X5),k1_tarski(X4)))),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2))))))),k1_tarski(X1)))),k1_tarski(X0)))) ),
    inference(definition_unfolding,[],[f23,f25,f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))))),k1_tarski(X0)))) ),
    inference(definition_unfolding,[],[f22,f25,f27])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:42:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.40  % (6656)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.41  % (6656)Refutation not found, incomplete strategy% (6656)------------------------------
% 0.20/0.41  % (6656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (6656)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.41  
% 0.20/0.41  % (6656)Memory used [KB]: 10618
% 0.20/0.41  % (6656)Time elapsed: 0.003 s
% 0.20/0.41  % (6656)------------------------------
% 0.20/0.41  % (6656)------------------------------
% 0.20/0.44  % (6657)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.44  % (6657)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(subsumption_resolution,[],[f41,f33])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0)))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f20,f25,f25,f25,f25])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f18,f16])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))))),
% 0.20/0.44    inference(forward_demodulation,[],[f40,f33])).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK0)))))))),
% 0.20/0.44    inference(forward_demodulation,[],[f32,f33])).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0)))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))))))),
% 0.20/0.44    inference(definition_unfolding,[],[f15,f31,f25,f28,f27])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))))))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f21,f25,f26,f26])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0))))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f17,f25])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))))))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f19,f25,f26])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3))))))),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3))))))),k1_tarski(X2)))),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3))))))),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k3_xboole_0(k5_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X6),k3_xboole_0(k1_tarski(X6),k1_tarski(X5)))),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3))))))),k1_tarski(X2)))),k1_tarski(X1)))),k1_tarski(X0))))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f24,f25,f30])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k1_tarski(X5),k3_xboole_0(k1_tarski(X5),k1_tarski(X4)))),k3_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k1_tarski(X5),k3_xboole_0(k1_tarski(X5),k1_tarski(X4)))),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k1_tarski(X5),k3_xboole_0(k1_tarski(X5),k1_tarski(X4)))),k3_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k1_tarski(X5),k3_xboole_0(k1_tarski(X5),k1_tarski(X4)))),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2))))))),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k1_tarski(X5),k3_xboole_0(k1_tarski(X5),k1_tarski(X4)))),k3_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k1_tarski(X5),k3_xboole_0(k1_tarski(X5),k1_tarski(X4)))),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k1_tarski(X5),k3_xboole_0(k1_tarski(X5),k1_tarski(X4)))),k3_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k1_tarski(X5),k3_xboole_0(k1_tarski(X5),k1_tarski(X4)))),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2))))))),k1_tarski(X1)))),k1_tarski(X0))))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f23,f25,f29])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k1_tarski(X3)))),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))))),k1_tarski(X0))))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f22,f25,f27])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6))),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f12,f13])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.20/0.44    inference(ennf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.20/0.44    inference(negated_conjecture,[],[f10])).
% 0.20/0.44  fof(f10,conjecture,(
% 0.20/0.44    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (6657)------------------------------
% 0.20/0.44  % (6657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (6657)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (6657)Memory used [KB]: 1791
% 0.20/0.44  % (6657)Time elapsed: 0.047 s
% 0.20/0.44  % (6657)------------------------------
% 0.20/0.44  % (6657)------------------------------
% 0.20/0.45  % (6644)Success in time 0.094 s
%------------------------------------------------------------------------------
