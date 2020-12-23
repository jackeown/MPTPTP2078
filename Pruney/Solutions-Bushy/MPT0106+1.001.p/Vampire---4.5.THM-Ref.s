%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0106+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   17 (  19 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    7
%              Number of atoms          :   18 (  20 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f259,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f250])).

fof(f250,plain,(
    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) ),
    inference(superposition,[],[f13,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X0,X1)),X2) = k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(X4,X2)),k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[],[f17,f11])).

fof(f11,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X3),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,X2)) ),
    inference(superposition,[],[f12,f11])).

fof(f12,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f13,plain,(
    k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) ),
    inference(definition_unfolding,[],[f9,f10])).

fof(f10,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f9,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))
   => k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_xboole_1)).

%------------------------------------------------------------------------------
