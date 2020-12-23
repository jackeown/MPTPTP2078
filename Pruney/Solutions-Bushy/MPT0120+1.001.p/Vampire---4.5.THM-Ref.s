%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0120+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:23 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   12 (  16 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    8
%              Number of atoms          :   13 (  17 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f16])).

fof(f16,plain,(
    k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))) != k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))) ),
    inference(forward_demodulation,[],[f15,f8])).

fof(f8,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f15,plain,(
    k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3)) != k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))) ),
    inference(forward_demodulation,[],[f11,f8])).

fof(f11,plain,(
    k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3)) != k2_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f7,f8])).

fof(f7,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) != k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) != k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f4,f5])).

fof(f5,plain,
    ( ? [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) != k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3))
   => k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) != k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3)) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) != k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_xboole_1)).

%------------------------------------------------------------------------------
