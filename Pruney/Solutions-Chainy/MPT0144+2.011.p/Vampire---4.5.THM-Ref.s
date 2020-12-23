%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 167 expanded)
%              Number of leaves         :   11 (  65 expanded)
%              Depth                    :   18
%              Number of atoms          :   46 ( 168 expanded)
%              Number of equality atoms :   45 ( 167 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f163,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f162])).

fof(f162,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f161,f41])).

fof(f41,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(k4_xboole_0(X4,X3),k4_xboole_0(X5,k5_xboole_0(X3,k4_xboole_0(X4,X3))))) = k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),X3)) ),
    inference(superposition,[],[f34,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
    inference(definition_unfolding,[],[f21,f18,f18,f18,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f21,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f161,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f160,f20])).

fof(f160,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f159,f41])).

fof(f159,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f158,f20])).

fof(f158,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f157,f41])).

fof(f157,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1)),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1)))))),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f155,f20])).

fof(f155,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(superposition,[],[f154,f34])).

fof(f154,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f153,f41])).

fof(f153,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2)),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f152,f20])).

fof(f152,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f151,f41])).

fof(f151,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1)),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1)))))),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f33,f20])).

fof(f33,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) ),
    inference(definition_unfolding,[],[f16,f32,f18,f31,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f17,f18])).

fof(f17,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f23,f18,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f22,f18,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f19,f18,f27])).

fof(f19,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X6),k1_tarski(X5))),k1_tarski(X4))),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f26,f18,f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k1_tarski(X3))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))))) ),
    inference(definition_unfolding,[],[f25,f18,f28,f28])).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

fof(f16,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.40  % (11037)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.45  % (11034)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.45  % (11029)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (11030)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (11032)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (11029)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f163,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f162])).
% 0.20/0.46  fof(f162,plain,(
% 0.20/0.46    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))),
% 0.20/0.46    inference(forward_demodulation,[],[f161,f41])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(k4_xboole_0(X4,X3),k4_xboole_0(X5,k5_xboole_0(X3,k4_xboole_0(X4,X3))))) = k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),X3))) )),
% 0.20/0.46    inference(superposition,[],[f34,f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f21,f18,f18,f18,f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.20/0.46  fof(f161,plain,(
% 0.20/0.46    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))),
% 0.20/0.46    inference(forward_demodulation,[],[f160,f20])).
% 0.20/0.46  fof(f160,plain,(
% 0.20/0.46    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))),
% 0.20/0.46    inference(forward_demodulation,[],[f159,f41])).
% 0.20/0.46  fof(f159,plain,(
% 0.20/0.46    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK1))),k1_tarski(sK0)))),
% 0.20/0.46    inference(forward_demodulation,[],[f158,f20])).
% 0.20/0.46  fof(f158,plain,(
% 0.20/0.46    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))),k1_tarski(sK1))),k1_tarski(sK0)))),
% 0.20/0.46    inference(forward_demodulation,[],[f157,f41])).
% 0.20/0.46  fof(f157,plain,(
% 0.20/0.46    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1)),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1)))))),k1_tarski(sK0)))),
% 0.20/0.46    inference(forward_demodulation,[],[f155,f20])).
% 0.20/0.46  fof(f155,plain,(
% 0.20/0.46    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))),
% 0.20/0.46    inference(superposition,[],[f154,f34])).
% 0.20/0.46  fof(f154,plain,(
% 0.20/0.46    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))),
% 0.20/0.46    inference(forward_demodulation,[],[f153,f41])).
% 0.20/0.46  fof(f153,plain,(
% 0.20/0.46    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2)),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))))),k1_tarski(sK1))),k1_tarski(sK0)))),
% 0.20/0.46    inference(forward_demodulation,[],[f152,f20])).
% 0.20/0.46  fof(f152,plain,(
% 0.20/0.46    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))))),k1_tarski(sK1))),k1_tarski(sK0)))),
% 0.20/0.46    inference(forward_demodulation,[],[f151,f41])).
% 0.20/0.46  fof(f151,plain,(
% 0.20/0.46    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1)),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1)))))),k1_tarski(sK0)))),
% 0.20/0.46    inference(forward_demodulation,[],[f33,f20])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))))),
% 0.20/0.46    inference(definition_unfolding,[],[f16,f32,f18,f31,f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f17,f18])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f23,f18,f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f22,f18,f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f19,f18,f27])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X6),k1_tarski(X5))),k1_tarski(X4))),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))))),k1_tarski(X0)))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f26,f18,f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k1_tarski(X3))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0)))))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f25,f18,f28,f28])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f13,f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.20/0.46    inference(ennf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.20/0.46    inference(negated_conjecture,[],[f11])).
% 0.20/0.46  fof(f11,conjecture,(
% 0.20/0.46    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (11029)------------------------------
% 0.20/0.46  % (11029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (11029)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (11029)Memory used [KB]: 6268
% 0.20/0.46  % (11029)Time elapsed: 0.057 s
% 0.20/0.46  % (11029)------------------------------
% 0.20/0.46  % (11029)------------------------------
% 0.20/0.46  % (11024)Success in time 0.111 s
%------------------------------------------------------------------------------
