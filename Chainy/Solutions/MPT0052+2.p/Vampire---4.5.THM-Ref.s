%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0052+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   15 (  20 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   25 (  37 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f339,plain,(
    $false ),
    inference(subsumption_resolution,[],[f338,f334])).

fof(f334,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f198,f246])).

fof(f246,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f198,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f148])).

fof(f148,plain,
    ( sK1 != k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f99,f147])).

fof(f147,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) != X1
        & r1_tarski(X0,X1) )
   => ( sK1 != k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f99,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) != X1
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f83])).

fof(f83,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(negated_conjecture,[],[f82])).

fof(f82,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f338,plain,(
    sK1 != k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f199,f249])).

fof(f249,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f199,plain,(
    sK1 != k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f148])).
%------------------------------------------------------------------------------
