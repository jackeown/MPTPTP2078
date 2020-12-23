%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0852+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   16 (  37 expanded)
%              Number of leaves         :    4 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :   25 (  71 expanded)
%              Number of equality atoms :   24 (  70 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1884,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1883,f1504])).

fof(f1504,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f1361])).

fof(f1361,plain,
    ( sK0 != k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))
    & sK0 = k4_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f1305,f1360,f1359])).

fof(f1359,plain,
    ( ? [X0] :
        ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) != X0
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( sK0 != k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))
      & ? [X2,X1] : k4_tarski(X1,X2) = sK0 ) ),
    introduced(choice_axiom,[])).

fof(f1360,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK0
   => sK0 = k4_tarski(sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f1305,plain,(
    ? [X0] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) != X0
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f1300])).

fof(f1300,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(negated_conjecture,[],[f1299])).

fof(f1299,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_mcart_1)).

fof(f1883,plain,(
    sK0 != k4_tarski(sK1,sK2) ),
    inference(forward_demodulation,[],[f1882,f1740])).

fof(f1740,plain,(
    k2_mcart_1(sK0) = sK2 ),
    inference(superposition,[],[f1507,f1504])).

fof(f1507,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f1298])).

fof(f1298,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f1882,plain,(
    sK0 != k4_tarski(sK1,k2_mcart_1(sK0)) ),
    inference(backward_demodulation,[],[f1505,f1739])).

fof(f1739,plain,(
    k1_mcart_1(sK0) = sK1 ),
    inference(superposition,[],[f1506,f1504])).

fof(f1506,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f1298])).

fof(f1505,plain,(
    sK0 != k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) ),
    inference(cnf_transformation,[],[f1361])).
%------------------------------------------------------------------------------
