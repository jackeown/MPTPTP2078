%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0334+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:24 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   23 (  35 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :    9
%              Number of atoms          :   36 (  64 expanded)
%              Number of equality atoms :   35 (  63 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f816,plain,(
    $false ),
    inference(subsumption_resolution,[],[f807,f608])).

fof(f608,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f540])).

fof(f540,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f491])).

fof(f491,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f368])).

fof(f368,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f807,plain,(
    k1_tarski(k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK2,k1_tarski(sK1)))) = k4_xboole_0(k1_tarski(k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK2,k1_tarski(sK1)))),k1_tarski(k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK2,k1_tarski(sK1))))) ),
    inference(backward_demodulation,[],[f672,f806])).

fof(f806,plain,(
    ! [X15] : k4_xboole_0(k2_xboole_0(X15,k1_tarski(sK0)),k1_tarski(sK1)) = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(X15,k1_tarski(sK1))) ),
    inference(forward_demodulation,[],[f795,f559])).

fof(f559,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f795,plain,(
    ! [X15] : k4_xboole_0(k2_xboole_0(X15,k1_tarski(sK0)),k1_tarski(sK1)) = k2_xboole_0(k4_xboole_0(X15,k1_tarski(sK1)),k1_tarski(sK0)) ),
    inference(superposition,[],[f538,f621])).

fof(f621,plain,(
    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f519,f541])).

fof(f541,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f491])).

fof(f519,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f483])).

fof(f483,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))
    & sK0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f443,f482])).

fof(f482,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0))
        & X0 != X1 )
   => ( k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))
      & sK0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f443,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f361])).

fof(f361,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( X0 != X1
       => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f360])).

fof(f360,conjecture,(
    ! [X0,X1,X2] :
      ( X0 != X1
     => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_zfmisc_1)).

fof(f538,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f672,plain,(
    k1_tarski(k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1))) = k4_xboole_0(k1_tarski(k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1))),k1_tarski(k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK2,k1_tarski(sK1))))) ),
    inference(unit_resulting_resolution,[],[f619,f541])).

fof(f619,plain,(
    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK2,k1_tarski(sK1))) ),
    inference(forward_demodulation,[],[f520,f559])).

fof(f520,plain,(
    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f483])).
%------------------------------------------------------------------------------
