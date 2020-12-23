%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   30 ( 102 expanded)
%              Number of leaves         :    9 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   31 ( 103 expanded)
%              Number of equality atoms :   30 ( 102 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :   12 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f47,plain,(
    $false ),
    inference(subsumption_resolution,[],[f46,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2)),X3)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3)))) ),
    inference(definition_unfolding,[],[f19,f16,f16,f16,f16,f16,f16])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_xboole_1)).

fof(f46,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5))))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)))))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5))))))) ),
    inference(forward_demodulation,[],[f45,f29])).

fof(f45,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5))))) ),
    inference(forward_demodulation,[],[f28,f29])).

fof(f28,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5))) ),
    inference(definition_unfolding,[],[f14,f27,f16,f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4))) ),
    inference(definition_unfolding,[],[f20,f16,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3))) ),
    inference(definition_unfolding,[],[f18,f16,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))) ),
    inference(definition_unfolding,[],[f17,f16,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))) ),
    inference(definition_unfolding,[],[f15,f16])).

fof(f15,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f17,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4))),k1_tarski(X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4))),k1_tarski(X5)))),k3_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4))),k1_tarski(X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4))),k1_tarski(X5))))) ),
    inference(definition_unfolding,[],[f21,f16,f26])).

fof(f21,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(f14,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))
   => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:48:21 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.43  % (20467)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.43  % (20468)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.43  % (20467)Refutation not found, incomplete strategy% (20467)------------------------------
% 0.22/0.43  % (20467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (20467)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.43  
% 0.22/0.43  % (20467)Memory used [KB]: 10618
% 0.22/0.43  % (20467)Time elapsed: 0.003 s
% 0.22/0.43  % (20467)------------------------------
% 0.22/0.43  % (20467)------------------------------
% 0.22/0.44  % (20468)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(subsumption_resolution,[],[f46,f29])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X2)),X3)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3))))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f19,f16,f16,f16,f16,f16,f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_xboole_1)).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5))))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)))))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)))))))),
% 0.22/0.44    inference(forward_demodulation,[],[f45,f29])).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)))))),
% 0.22/0.44    inference(forward_demodulation,[],[f28,f29])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))),k1_tarski(sK3))),k1_tarski(sK4))),k1_tarski(sK5)))),
% 0.22/0.44    inference(definition_unfolding,[],[f14,f27,f16,f26])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f20,f16,f25])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2))),k1_tarski(X3)))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f18,f16,f24])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f17,f16,f23])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f15,f16])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4))),k1_tarski(X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4))),k1_tarski(X5)))),k3_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4))),k1_tarski(X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4))),k1_tarski(X5)))))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f21,f16,f26])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5))),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5))),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.22/0.44    inference(ennf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.22/0.44    inference(negated_conjecture,[],[f9])).
% 0.22/0.44  fof(f9,conjecture,(
% 0.22/0.44    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (20468)------------------------------
% 0.22/0.44  % (20468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (20468)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (20468)Memory used [KB]: 1918
% 0.22/0.44  % (20468)Time elapsed: 0.006 s
% 0.22/0.44  % (20468)------------------------------
% 0.22/0.44  % (20468)------------------------------
% 0.22/0.44  % (20455)Success in time 0.068 s
%------------------------------------------------------------------------------
