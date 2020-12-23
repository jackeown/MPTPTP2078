%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0025+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   16 (  21 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    7
%              Number of atoms          :   32 (  44 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f223,plain,(
    $false ),
    inference(subsumption_resolution,[],[f215,f173])).

fof(f173,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f215,plain,(
    ~ r1_tarski(k3_xboole_0(sK6,sK7),sK6) ),
    inference(resolution,[],[f211,f140])).

fof(f140,plain,(
    r1_tarski(sK5,k3_xboole_0(sK6,sK7)) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,
    ( ~ r1_tarski(sK5,sK6)
    & r1_tarski(sK5,k3_xboole_0(sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f66,f99])).

fof(f99,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k3_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK5,sK6)
      & r1_tarski(sK5,k3_xboole_0(sK6,sK7)) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f49,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f48])).

fof(f48,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f211,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK5,X0)
      | ~ r1_tarski(X0,sK6) ) ),
    inference(resolution,[],[f141,f148])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f51,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f141,plain,(
    ~ r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f100])).
%------------------------------------------------------------------------------
