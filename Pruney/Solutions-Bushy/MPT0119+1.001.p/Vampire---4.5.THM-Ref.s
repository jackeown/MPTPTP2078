%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0119+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   22 (  30 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :   12
%              Number of atoms          :   23 (  31 expanded)
%              Number of equality atoms :   22 (  30 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f39])).

fof(f39,plain,(
    k3_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0))) != k3_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0))) ),
    inference(superposition,[],[f32,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f32,plain,(
    k3_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0))) != k2_xboole_0(k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)),k3_xboole_0(sK1,k4_xboole_0(sK2,sK0))) ),
    inference(forward_demodulation,[],[f31,f11])).

fof(f11,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f31,plain,(
    k3_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0))) != k2_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK1,k4_xboole_0(sK2,sK0))) ),
    inference(forward_demodulation,[],[f30,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_xboole_1)).

fof(f30,plain,(
    k3_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0))) != k2_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK2,sK0))) ),
    inference(forward_demodulation,[],[f29,f11])).

fof(f29,plain,(
    k3_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0))) != k2_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(k4_xboole_0(sK2,sK0),sK1)) ),
    inference(forward_demodulation,[],[f28,f14])).

fof(f28,plain,(
    k2_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k4_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(sK0,sK1))) != k3_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0))) ),
    inference(forward_demodulation,[],[f15,f11])).

fof(f15,plain,(
    k2_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k4_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(sK0,sK1))) != k3_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0)),sK1) ),
    inference(definition_unfolding,[],[f10,f12,f12])).

fof(f12,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f10,plain,(
    k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k5_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k5_xboole_0(sK0,sK2),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k5_xboole_0(X0,X2),X1)
   => k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k5_xboole_0(sK0,sK2),sK1) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

%------------------------------------------------------------------------------
