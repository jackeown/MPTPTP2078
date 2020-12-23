%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0012+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   19 (  23 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    9
%              Number of atoms          :   20 (  24 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f136])).

fof(f136,plain,(
    k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f135,f72])).

fof(f72,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f135,plain,(
    k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,sK2))) ),
    inference(forward_demodulation,[],[f134,f104])).

fof(f104,plain,(
    ! [X8,X7,X9] : k2_xboole_0(X7,k2_xboole_0(X8,X9)) = k2_xboole_0(X9,k2_xboole_0(X7,X8)) ),
    inference(superposition,[],[f68,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f68,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f134,plain,(
    k2_xboole_0(sK0,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f77,f68])).

fof(f77,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK2)) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f61,f68])).

fof(f61,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f51,f54])).

fof(f54,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
   => k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f45])).

fof(f45,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_1)).
%------------------------------------------------------------------------------
