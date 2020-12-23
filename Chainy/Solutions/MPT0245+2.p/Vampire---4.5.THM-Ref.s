%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0245+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   16 (  28 expanded)
%              Number of leaves         :    3 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   40 (  82 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1593,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1592,f623])).

fof(f623,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f497])).

fof(f497,plain,
    ( ~ r1_tarski(sK4,k4_xboole_0(sK5,k1_tarski(sK6)))
    & ~ r2_hidden(sK6,sK4)
    & r1_tarski(sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f352,f496])).

fof(f496,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
        & ~ r2_hidden(X2,X0)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(sK4,k4_xboole_0(sK5,k1_tarski(sK6)))
      & ~ r2_hidden(sK6,sK4)
      & r1_tarski(sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f352,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      & ~ r2_hidden(X2,X0)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f351])).

fof(f351,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      & ~ r2_hidden(X2,X0)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f341])).

fof(f341,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
          | r2_hidden(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f340])).

fof(f340,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_zfmisc_1)).

fof(f1592,plain,(
    ~ r1_tarski(sK4,sK5) ),
    inference(subsumption_resolution,[],[f1577,f624])).

fof(f624,plain,(
    ~ r2_hidden(sK6,sK4) ),
    inference(cnf_transformation,[],[f497])).

fof(f1577,plain,
    ( r2_hidden(sK6,sK4)
    | ~ r1_tarski(sK4,sK5) ),
    inference(resolution,[],[f625,f865])).

fof(f865,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f420])).

fof(f420,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f419])).

fof(f419,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f300])).

fof(f300,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l2_zfmisc_1)).

fof(f625,plain,(
    ~ r1_tarski(sK4,k4_xboole_0(sK5,k1_tarski(sK6))) ),
    inference(cnf_transformation,[],[f497])).
%------------------------------------------------------------------------------
