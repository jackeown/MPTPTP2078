%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0302+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:22 EST 2020

% Result     : Theorem 2.35s
% Output     : Refutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 110 expanded)
%              Number of leaves         :    9 (  27 expanded)
%              Depth                    :   17
%              Number of atoms          :  167 ( 411 expanded)
%              Number of equality atoms :   45 ( 162 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2531,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2515,f790])).

fof(f790,plain,(
    k1_xboole_0 != sK27 ),
    inference(cnf_transformation,[],[f611])).

fof(f611,plain,
    ( sK27 != sK28
    & k1_xboole_0 != sK28
    & k1_xboole_0 != sK27
    & k2_zfmisc_1(sK27,sK28) = k2_zfmisc_1(sK28,sK27) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK27,sK28])],[f408,f610])).

fof(f610,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) )
   => ( sK27 != sK28
      & k1_xboole_0 != sK28
      & k1_xboole_0 != sK27
      & k2_zfmisc_1(sK27,sK28) = k2_zfmisc_1(sK28,sK27) ) ),
    introduced(choice_axiom,[])).

fof(f408,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f407])).

fof(f407,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f322])).

fof(f322,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f321])).

fof(f321,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(f2515,plain,(
    k1_xboole_0 = sK27 ),
    inference(resolution,[],[f2496,f849])).

fof(f849,plain,(
    ! [X0] :
      ( r2_hidden(sK31(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f638])).

fof(f638,plain,(
    ! [X0] :
      ( r2_hidden(sK31(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK31])],[f423,f637])).

fof(f637,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK31(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f423,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f2496,plain,(
    ! [X7] : ~ r2_hidden(X7,sK27) ),
    inference(subsumption_resolution,[],[f2479,f791])).

fof(f791,plain,(
    k1_xboole_0 != sK28 ),
    inference(cnf_transformation,[],[f611])).

fof(f2479,plain,(
    ! [X7] :
      ( ~ r2_hidden(X7,sK27)
      | k1_xboole_0 = sK28 ) ),
    inference(resolution,[],[f2468,f849])).

fof(f2468,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK28)
      | ~ r2_hidden(X0,sK27) ) ),
    inference(resolution,[],[f2466,f2309])).

fof(f2309,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK28,sK27)
      | ~ r2_hidden(X0,sK28) ) ),
    inference(subsumption_resolution,[],[f2307,f792])).

fof(f792,plain,(
    sK27 != sK28 ),
    inference(cnf_transformation,[],[f611])).

fof(f2307,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK28)
      | sK27 = sK28
      | ~ r1_tarski(sK28,sK27) ) ),
    inference(resolution,[],[f2305,f1084])).

fof(f1084,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f746])).

fof(f746,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f745])).

fof(f745,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2305,plain,(
    ! [X3] :
      ( r1_tarski(sK27,sK28)
      | ~ r2_hidden(X3,sK28) ) ),
    inference(duplicate_literal_removal,[],[f2304])).

fof(f2304,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK28)
      | r1_tarski(sK27,sK28)
      | r1_tarski(sK27,sK28) ) ),
    inference(resolution,[],[f1597,f1057])).

fof(f1057,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK47(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f733])).

fof(f733,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK47(X0,X1),X1)
          & r2_hidden(sK47(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK47])],[f731,f732])).

fof(f732,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK47(X0,X1),X1)
        & r2_hidden(sK47(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f731,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f730])).

fof(f730,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f488])).

fof(f488,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f1597,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(sK47(X9,sK28),sK27)
      | ~ r2_hidden(X8,sK28)
      | r1_tarski(X9,sK28) ) ),
    inference(resolution,[],[f1516,f1058])).

fof(f1058,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK47(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f733])).

fof(f1516,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,sK28)
      | ~ r2_hidden(X3,sK28)
      | ~ r2_hidden(X2,sK27) ) ),
    inference(resolution,[],[f1463,f875])).

fof(f875,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f652])).

fof(f652,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f651])).

fof(f651,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f316])).

fof(f316,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f1463,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK27,sK28))
      | r2_hidden(X2,sK28) ) ),
    inference(superposition,[],[f870,f789])).

fof(f789,plain,(
    k2_zfmisc_1(sK27,sK28) = k2_zfmisc_1(sK28,sK27) ),
    inference(cnf_transformation,[],[f611])).

fof(f870,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f650])).

fof(f650,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f649])).

fof(f649,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f310])).

fof(f310,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f2466,plain,(
    ! [X3] :
      ( r1_tarski(sK28,sK27)
      | ~ r2_hidden(X3,sK27) ) ),
    inference(duplicate_literal_removal,[],[f2465])).

fof(f2465,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK27)
      | r1_tarski(sK28,sK27)
      | r1_tarski(sK28,sK27) ) ),
    inference(resolution,[],[f1603,f1057])).

fof(f1603,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(sK47(X8,sK27),sK28)
      | ~ r2_hidden(X9,sK27)
      | r1_tarski(X8,sK27) ) ),
    inference(resolution,[],[f1575,f1058])).

fof(f1575,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,sK27)
      | ~ r2_hidden(X2,sK28)
      | ~ r2_hidden(X3,sK27) ) ),
    inference(resolution,[],[f1464,f875])).

fof(f1464,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK27,sK28))
      | r2_hidden(X5,sK27) ) ),
    inference(superposition,[],[f871,f789])).

fof(f871,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f650])).
%------------------------------------------------------------------------------
