%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0064+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   12 (  17 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    6
%              Number of atoms          :   22 (  34 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f364,plain,(
    $false ),
    inference(subsumption_resolution,[],[f362,f203])).

fof(f203,plain,(
    r2_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f162])).

fof(f162,plain,
    ( r2_xboole_0(sK4,sK3)
    & r2_xboole_0(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f111,f161])).

fof(f161,plain,
    ( ? [X0,X1] :
        ( r2_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) )
   => ( r2_xboole_0(sK4,sK3)
      & r2_xboole_0(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f111,plain,(
    ? [X0,X1] :
      ( r2_xboole_0(X1,X0)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f99])).

fof(f99,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( r2_xboole_0(X1,X0)
          & r2_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f98])).

fof(f98,conjecture,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_xboole_1)).

fof(f362,plain,(
    ~ r2_xboole_0(sK4,sK3) ),
    inference(resolution,[],[f202,f211])).

fof(f211,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f202,plain,(
    r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f162])).
%------------------------------------------------------------------------------
