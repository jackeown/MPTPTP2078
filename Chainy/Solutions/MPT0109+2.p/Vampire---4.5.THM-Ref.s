%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0109+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :    9
%              Number of atoms          :   20 (  20 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f517,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f516])).

fof(f516,plain,(
    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f515,f359])).

fof(f359,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f515,plain,(
    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) ),
    inference(forward_demodulation,[],[f512,f355])).

fof(f355,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).

fof(f512,plain,(
    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f511,f327])).

fof(f327,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f511,plain,(
    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f308,f334])).

fof(f334,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f308,plain,(
    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)) ),
    inference(cnf_transformation,[],[f253])).

fof(f253,plain,(
    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f160,f252])).

fof(f252,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2))
   => k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)) ),
    introduced(choice_axiom,[])).

fof(f160,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(ennf_transformation,[],[f48])).

fof(f48,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(negated_conjecture,[],[f47])).

fof(f47,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_xboole_1)).
%------------------------------------------------------------------------------
