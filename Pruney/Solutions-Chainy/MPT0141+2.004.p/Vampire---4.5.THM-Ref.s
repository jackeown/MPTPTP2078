%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  96 expanded)
%              Number of leaves         :    9 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   30 (  97 expanded)
%              Number of equality atoms :   29 (  96 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :   12 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,plain,(
    $false ),
    inference(subsumption_resolution,[],[f28,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2)),X3)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3)))) ),
    inference(definition_unfolding,[],[f18,f15,f15,f15,f15,f15,f15])).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_xboole_1)).

fof(f28,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6))))))) ),
    inference(backward_demodulation,[],[f26,f27])).

fof(f26,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5))),k1_tarski(sK6)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5))),k1_tarski(sK6)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5))),k1_tarski(sK6)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5))),k1_tarski(sK6))))) ),
    inference(definition_unfolding,[],[f13,f24,f15,f21,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4))) ),
    inference(definition_unfolding,[],[f19,f15,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3))) ),
    inference(definition_unfolding,[],[f17,f15,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))) ),
    inference(definition_unfolding,[],[f16,f15,f21])).

fof(f16,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f19,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))) ),
    inference(definition_unfolding,[],[f14,f15])).

fof(f14,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X5)),k3_xboole_0(k1_tarski(X4),k1_tarski(X5))),k1_tarski(X6)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X5)),k3_xboole_0(k1_tarski(X4),k1_tarski(X5))),k1_tarski(X6)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X5)),k3_xboole_0(k1_tarski(X4),k1_tarski(X5))),k1_tarski(X6)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X5)),k3_xboole_0(k1_tarski(X4),k1_tarski(X5))),k1_tarski(X6))))) ),
    inference(definition_unfolding,[],[f20,f15,f23,f22])).

fof(f20,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

fof(f13,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:52:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (12059)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (12059)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f28,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2)),X3)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3))))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f18,f15,f15,f15,f15,f15,f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_xboole_1)).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)))))))),
% 0.21/0.47    inference(backward_demodulation,[],[f26,f27])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k1_tarski(sK6))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5))),k1_tarski(sK6)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5))),k1_tarski(sK6)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5))),k1_tarski(sK6)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5))),k1_tarski(sK6)))))),
% 0.21/0.47    inference(definition_unfolding,[],[f13,f24,f15,f21,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f19,f15,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f17,f15,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f16,f15,f21])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f14,f15])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X5)),k3_xboole_0(k1_tarski(X4),k1_tarski(X5))),k1_tarski(X6)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X5)),k3_xboole_0(k1_tarski(X4),k1_tarski(X5))),k1_tarski(X6)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X5)),k3_xboole_0(k1_tarski(X4),k1_tarski(X5))),k1_tarski(X6)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X5)),k3_xboole_0(k1_tarski(X4),k1_tarski(X5))),k1_tarski(X6)))))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f20,f15,f23,f22])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6))),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f10,f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 0.21/0.47    inference(negated_conjecture,[],[f8])).
% 0.21/0.47  fof(f8,conjecture,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (12059)------------------------------
% 0.21/0.47  % (12059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (12059)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (12059)Memory used [KB]: 1791
% 0.21/0.47  % (12059)Time elapsed: 0.008 s
% 0.21/0.47  % (12059)------------------------------
% 0.21/0.47  % (12059)------------------------------
% 0.21/0.47  % (12045)Success in time 0.109 s
%------------------------------------------------------------------------------
