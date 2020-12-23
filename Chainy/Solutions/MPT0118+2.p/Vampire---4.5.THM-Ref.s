%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0118+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:10 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   14 (  18 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    8
%              Number of atoms          :   15 (  19 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f282,plain,(
    $false ),
    inference(subsumption_resolution,[],[f281,f241])).

fof(f241,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f109])).

fof(f109,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

fof(f281,plain,(
    k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f280,f253])).

fof(f253,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f280,plain,(
    k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f279,f253])).

fof(f279,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f211,f253])).

fof(f211,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f204])).

fof(f204,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f170,f203])).

fof(f203,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k4_xboole_0(X0,X2),X1)
   => k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(choice_axiom,[])).

fof(f170,plain,(
    ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(ennf_transformation,[],[f61])).

fof(f61,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(negated_conjecture,[],[f60])).

fof(f60,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_xboole_1)).
%------------------------------------------------------------------------------
