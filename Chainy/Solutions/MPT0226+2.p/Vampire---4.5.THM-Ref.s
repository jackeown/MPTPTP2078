%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0226+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   27 (  46 expanded)
%              Number of leaves         :    7 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :   38 (  64 expanded)
%              Number of equality atoms :   37 (  63 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f975,plain,(
    $false ),
    inference(subsumption_resolution,[],[f974,f569])).

fof(f569,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f974,plain,(
    k1_enumset1(sK14,sK14,sK14) != k4_xboole_0(k1_enumset1(sK14,sK14,sK14),k1_xboole_0) ),
    inference(forward_demodulation,[],[f973,f877])).

fof(f877,plain,(
    k1_xboole_0 = k4_xboole_0(k1_enumset1(sK14,sK14,sK14),k1_enumset1(sK15,sK15,sK15)) ),
    inference(forward_demodulation,[],[f876,f747])).

fof(f747,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f256])).

fof(f256,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f876,plain,(
    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK14,sK14,sK14,sK14),k1_enumset1(sK15,sK15,sK15)) ),
    inference(forward_demodulation,[],[f768,f747])).

fof(f768,plain,(
    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK14,sK14,sK14,sK14),k2_enumset1(sK15,sK15,sK15,sK15)) ),
    inference(definition_unfolding,[],[f514,f548,f548])).

fof(f548,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f267])).

fof(f267,axiom,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

fof(f514,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK14),k1_tarski(sK15)) ),
    inference(cnf_transformation,[],[f434])).

fof(f434,plain,
    ( sK14 != sK15
    & k1_xboole_0 = k4_xboole_0(k1_tarski(sK14),k1_tarski(sK15)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15])],[f319,f433])).

fof(f433,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK14 != sK15
      & k1_xboole_0 = k4_xboole_0(k1_tarski(sK14),k1_tarski(sK15)) ) ),
    introduced(choice_axiom,[])).

fof(f319,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f310])).

fof(f310,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f309])).

fof(f309,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(f973,plain,(
    k1_enumset1(sK14,sK14,sK14) != k4_xboole_0(k1_enumset1(sK14,sK14,sK14),k4_xboole_0(k1_enumset1(sK14,sK14,sK14),k1_enumset1(sK15,sK15,sK15))) ),
    inference(forward_demodulation,[],[f972,f747])).

fof(f972,plain,(
    k2_enumset1(sK14,sK14,sK14,sK14) != k4_xboole_0(k2_enumset1(sK14,sK14,sK14,sK14),k4_xboole_0(k2_enumset1(sK14,sK14,sK14,sK14),k1_enumset1(sK15,sK15,sK15))) ),
    inference(forward_demodulation,[],[f898,f747])).

fof(f898,plain,(
    k2_enumset1(sK14,sK14,sK14,sK14) != k4_xboole_0(k2_enumset1(sK14,sK14,sK14,sK14),k4_xboole_0(k2_enumset1(sK14,sK14,sK14,sK14),k2_enumset1(sK15,sK15,sK15,sK15))) ),
    inference(unit_resulting_resolution,[],[f515,f784])).

fof(f784,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) ) ),
    inference(definition_unfolding,[],[f545,f548,f539,f548,f548])).

fof(f539,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f545,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f332])).

fof(f332,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f305])).

fof(f305,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f515,plain,(
    sK14 != sK15 ),
    inference(cnf_transformation,[],[f434])).
%------------------------------------------------------------------------------
