%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0303+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:23 EST 2020

% Result     : Theorem 2.02s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   40 (  81 expanded)
%              Number of leaves         :    6 (  19 expanded)
%              Depth                    :   13
%              Number of atoms          :  115 ( 276 expanded)
%              Number of equality atoms :   21 (  46 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2308,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2307,f2147])).

fof(f2147,plain,(
    ~ r1_tarski(sK28,sK27) ),
    inference(subsumption_resolution,[],[f2143,f792])).

fof(f792,plain,(
    sK27 != sK28 ),
    inference(cnf_transformation,[],[f613])).

fof(f613,plain,
    ( sK27 != sK28
    & k2_zfmisc_1(sK27,sK27) = k2_zfmisc_1(sK28,sK28) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK27,sK28])],[f408,f612])).

fof(f612,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) )
   => ( sK27 != sK28
      & k2_zfmisc_1(sK27,sK27) = k2_zfmisc_1(sK28,sK28) ) ),
    introduced(choice_axiom,[])).

fof(f408,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) ) ),
    inference(ennf_transformation,[],[f323])).

fof(f323,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f322])).

fof(f322,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_zfmisc_1)).

fof(f2143,plain,
    ( sK27 = sK28
    | ~ r1_tarski(sK28,sK27) ),
    inference(resolution,[],[f2139,f1027])).

fof(f1027,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f731])).

fof(f731,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f730])).

fof(f730,plain,(
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

fof(f2139,plain,(
    r1_tarski(sK27,sK28) ),
    inference(duplicate_literal_removal,[],[f2136])).

fof(f2136,plain,
    ( r1_tarski(sK27,sK28)
    | r1_tarski(sK27,sK28) ),
    inference(resolution,[],[f1572,f936])).

fof(f936,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK45(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f711])).

fof(f711,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK45(X0,X1),X1)
          & r2_hidden(sK45(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK45])],[f709,f710])).

fof(f710,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK45(X0,X1),X1)
        & r2_hidden(sK45(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f709,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f708])).

fof(f708,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f436])).

fof(f436,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f1572,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK45(X4,sK28),sK27)
      | r1_tarski(X4,sK28) ) ),
    inference(resolution,[],[f1566,f937])).

fof(f937,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK45(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f711])).

fof(f1566,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK28)
      | ~ r2_hidden(X0,sK27) ) ),
    inference(condensation,[],[f1558])).

fof(f1558,plain,(
    ! [X4,X5] :
      ( r2_hidden(X4,sK28)
      | ~ r2_hidden(X5,sK27)
      | ~ r2_hidden(X4,sK27) ) ),
    inference(resolution,[],[f1464,f806])).

fof(f806,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f625])).

fof(f625,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f624])).

fof(f624,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f1464,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK27,sK27))
      | r2_hidden(X2,sK28) ) ),
    inference(superposition,[],[f804,f791])).

fof(f791,plain,(
    k2_zfmisc_1(sK27,sK27) = k2_zfmisc_1(sK28,sK28) ),
    inference(cnf_transformation,[],[f613])).

fof(f804,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f625])).

fof(f2307,plain,(
    r1_tarski(sK28,sK27) ),
    inference(duplicate_literal_removal,[],[f2304])).

fof(f2304,plain,
    ( r1_tarski(sK28,sK27)
    | r1_tarski(sK28,sK27) ),
    inference(resolution,[],[f1851,f936])).

fof(f1851,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK45(X5,sK27),sK28)
      | r1_tarski(X5,sK27) ) ),
    inference(resolution,[],[f1840,f937])).

fof(f1840,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK27)
      | ~ r2_hidden(X0,sK28) ) ),
    inference(condensation,[],[f1826])).

fof(f1826,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X10,sK28)
      | ~ r2_hidden(X11,sK28)
      | r2_hidden(X10,sK27) ) ),
    inference(resolution,[],[f1466,f805])).

fof(f805,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f625])).

fof(f1466,plain,(
    ! [X6,X7] :
      ( r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(sK27,sK27))
      | ~ r2_hidden(X7,sK28)
      | ~ r2_hidden(X6,sK28) ) ),
    inference(superposition,[],[f806,f791])).
%------------------------------------------------------------------------------
