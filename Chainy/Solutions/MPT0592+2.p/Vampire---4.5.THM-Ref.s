%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0592+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:39 EST 2020

% Result     : Theorem 1.84s
% Output     : Refutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   24 (  56 expanded)
%              Number of leaves         :    4 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :   77 ( 264 expanded)
%              Number of equality atoms :   49 ( 168 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2618,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2617,f1593])).

fof(f1593,plain,(
    v1_relat_1(sK49) ),
    inference(cnf_transformation,[],[f1301])).

fof(f1301,plain,
    ( sK48 != sK49
    & k1_xboole_0 = k1_relat_1(sK49)
    & k1_xboole_0 = k1_relat_1(sK48)
    & v1_relat_1(sK49)
    & v1_relat_1(sK48) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK48,sK49])],[f860,f1300,f1299])).

fof(f1299,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & k1_xboole_0 = k1_relat_1(X1)
            & k1_xboole_0 = k1_relat_1(X0)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( sK48 != X1
          & k1_xboole_0 = k1_relat_1(X1)
          & k1_xboole_0 = k1_relat_1(sK48)
          & v1_relat_1(X1) )
      & v1_relat_1(sK48) ) ),
    introduced(choice_axiom,[])).

fof(f1300,plain,
    ( ? [X1] :
        ( sK48 != X1
        & k1_xboole_0 = k1_relat_1(X1)
        & k1_xboole_0 = k1_relat_1(sK48)
        & v1_relat_1(X1) )
   => ( sK48 != sK49
      & k1_xboole_0 = k1_relat_1(sK49)
      & k1_xboole_0 = k1_relat_1(sK48)
      & v1_relat_1(sK49) ) ),
    introduced(choice_axiom,[])).

fof(f860,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k1_relat_1(X1)
          & k1_xboole_0 = k1_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f859])).

fof(f859,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k1_relat_1(X1)
          & k1_xboole_0 = k1_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f787])).

fof(f787,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( ( k1_xboole_0 = k1_relat_1(X1)
                & k1_xboole_0 = k1_relat_1(X0) )
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f786])).

fof(f786,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( k1_xboole_0 = k1_relat_1(X1)
              & k1_xboole_0 = k1_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t196_relat_1)).

fof(f2617,plain,(
    ~ v1_relat_1(sK49) ),
    inference(subsumption_resolution,[],[f2604,f2574])).

fof(f2574,plain,(
    k1_xboole_0 != sK49 ),
    inference(backward_demodulation,[],[f1596,f2551])).

fof(f2551,plain,(
    k1_xboole_0 = sK48 ),
    inference(subsumption_resolution,[],[f2538,f1592])).

fof(f1592,plain,(
    v1_relat_1(sK48) ),
    inference(cnf_transformation,[],[f1301])).

fof(f2538,plain,
    ( k1_xboole_0 = sK48
    | ~ v1_relat_1(sK48) ),
    inference(trivial_inequality_removal,[],[f2528])).

fof(f2528,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK48
    | ~ v1_relat_1(sK48) ),
    inference(superposition,[],[f1643,f1594])).

fof(f1594,plain,(
    k1_xboole_0 = k1_relat_1(sK48) ),
    inference(cnf_transformation,[],[f1301])).

fof(f1643,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f902])).

fof(f902,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f901])).

fof(f901,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f824])).

fof(f824,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f1596,plain,(
    sK48 != sK49 ),
    inference(cnf_transformation,[],[f1301])).

fof(f2604,plain,
    ( k1_xboole_0 = sK49
    | ~ v1_relat_1(sK49) ),
    inference(trivial_inequality_removal,[],[f2594])).

fof(f2594,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK49
    | ~ v1_relat_1(sK49) ),
    inference(superposition,[],[f1643,f1595])).

fof(f1595,plain,(
    k1_xboole_0 = k1_relat_1(sK49) ),
    inference(cnf_transformation,[],[f1301])).
%------------------------------------------------------------------------------
