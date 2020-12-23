%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0232+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   28 (  64 expanded)
%              Number of leaves         :    6 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 ( 115 expanded)
%              Number of equality atoms :   24 (  59 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f730,plain,(
    $false ),
    inference(global_subsumption,[],[f688,f729])).

fof(f729,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f716,f589])).

fof(f589,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) ),
    inference(definition_unfolding,[],[f501,f544])).

fof(f544,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f226])).

fof(f226,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f501,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f301])).

fof(f301,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f716,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(resolution,[],[f687,f492])).

fof(f492,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f414])).

fof(f414,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f413])).

fof(f413,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f687,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f586,f648])).

fof(f648,plain,(
    sK0 = sK2 ),
    inference(resolution,[],[f586,f588])).

fof(f588,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2))
      | X0 = X2 ) ),
    inference(definition_unfolding,[],[f461,f544])).

fof(f461,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(cnf_transformation,[],[f357])).

fof(f357,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | ~ r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f315])).

fof(f315,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

fof(f586,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)) ),
    inference(definition_unfolding,[],[f429,f544])).

fof(f429,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f398])).

fof(f398,plain,
    ( k2_tarski(sK0,sK1) != k1_tarski(sK2)
    & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f324,f397])).

fof(f397,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X1) != k1_tarski(X2)
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( k2_tarski(sK0,sK1) != k1_tarski(sK2)
      & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f324,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k1_tarski(X2)
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f317])).

fof(f317,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    inference(negated_conjecture,[],[f316])).

fof(f316,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).

fof(f688,plain,(
    k1_tarski(sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(backward_demodulation,[],[f585,f648])).

fof(f585,plain,(
    k1_tarski(sK2) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(definition_unfolding,[],[f430,f544])).

fof(f430,plain,(
    k2_tarski(sK0,sK1) != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f398])).
%------------------------------------------------------------------------------
