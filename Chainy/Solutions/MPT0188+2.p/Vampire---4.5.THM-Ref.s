%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0188+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   18 (  20 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    9
%              Number of atoms          :   22 (  24 expanded)
%              Number of equality atoms :   21 (  23 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f876,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f875])).

fof(f875,plain,(
    k4_xboole_0(k2_enumset1(sK17,sK18,sK19,sK20),k2_enumset1(sK17,sK18,sK19,sK20)) != k4_xboole_0(k2_enumset1(sK17,sK18,sK19,sK20),k2_enumset1(sK17,sK18,sK19,sK20)) ),
    inference(forward_demodulation,[],[f874,f509])).

fof(f509,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f192])).

fof(f192,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

fof(f874,plain,(
    k4_xboole_0(k2_enumset1(sK17,sK18,sK19,sK20),k2_enumset1(sK17,sK18,sK20,sK19)) != k4_xboole_0(k2_enumset1(sK17,sK18,sK20,sK19),k2_enumset1(sK17,sK18,sK19,sK20)) ),
    inference(forward_demodulation,[],[f873,f508])).

fof(f508,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f194])).

fof(f194,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

fof(f873,plain,(
    k4_xboole_0(k2_enumset1(sK17,sK18,sK19,sK20),k2_enumset1(sK17,sK19,sK18,sK20)) != k4_xboole_0(k2_enumset1(sK17,sK19,sK18,sK20),k2_enumset1(sK17,sK18,sK19,sK20)) ),
    inference(forward_demodulation,[],[f866,f508])).

fof(f866,plain,(
    k4_xboole_0(k2_enumset1(sK17,sK18,sK19,sK20),k2_enumset1(sK17,sK20,sK19,sK18)) != k4_xboole_0(k2_enumset1(sK17,sK20,sK19,sK18),k2_enumset1(sK17,sK18,sK19,sK20)) ),
    inference(unit_resulting_resolution,[],[f493,f730])).

fof(f730,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f316])).

fof(f316,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f92])).

fof(f92,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f493,plain,(
    k2_enumset1(sK17,sK18,sK19,sK20) != k2_enumset1(sK17,sK20,sK19,sK18) ),
    inference(cnf_transformation,[],[f395])).

fof(f395,plain,(
    k2_enumset1(sK17,sK18,sK19,sK20) != k2_enumset1(sK17,sK20,sK19,sK18) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17,sK18,sK19,sK20])],[f260,f394])).

fof(f394,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X3,X2,X1)
   => k2_enumset1(sK17,sK18,sK19,sK20) != k2_enumset1(sK17,sK20,sK19,sK18) ),
    introduced(choice_axiom,[])).

fof(f260,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X3,X2,X1) ),
    inference(ennf_transformation,[],[f196])).

fof(f196,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(negated_conjecture,[],[f195])).

fof(f195,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).
%------------------------------------------------------------------------------
