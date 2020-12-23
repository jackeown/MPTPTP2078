%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0261+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:20 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   12 (  17 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    6
%              Number of atoms          :   22 (  34 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1589,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1574,f663])).

fof(f663,plain,(
    ~ r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f531])).

fof(f531,plain,
    ( ~ r1_xboole_0(k1_tarski(sK4),sK5)
    & ~ r2_hidden(sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f368,f530])).

fof(f530,plain,
    ( ? [X0,X1] :
        ( ~ r1_xboole_0(k1_tarski(X0),X1)
        & ~ r2_hidden(X0,X1) )
   => ( ~ r1_xboole_0(k1_tarski(sK4),sK5)
      & ~ r2_hidden(sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f368,plain,(
    ? [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      & ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f358])).

fof(f358,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
       => r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f357])).

fof(f357,conjecture,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_zfmisc_1)).

fof(f1574,plain,(
    r2_hidden(sK4,sK5) ),
    inference(resolution,[],[f664,f763])).

fof(f763,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f384])).

fof(f384,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f298])).

fof(f298,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f664,plain,(
    ~ r1_xboole_0(k1_tarski(sK4),sK5) ),
    inference(cnf_transformation,[],[f531])).
%------------------------------------------------------------------------------
