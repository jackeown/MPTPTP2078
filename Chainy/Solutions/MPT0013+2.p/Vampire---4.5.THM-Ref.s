%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0013+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   14 (  14 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    6
%              Number of atoms          :   15 (  15 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f328,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f326])).

fof(f326,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f77,f121])).

fof(f121,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f85,f89])).

fof(f89,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f85,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f77,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f52,f59])).

fof(f59,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(X0,k2_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f48])).

fof(f48,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f47])).

fof(f47,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).
%------------------------------------------------------------------------------
