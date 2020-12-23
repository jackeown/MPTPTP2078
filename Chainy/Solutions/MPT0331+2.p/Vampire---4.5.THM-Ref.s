%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0331+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   23 (  33 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 (  88 expanded)
%              Number of equality atoms :   12 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1283,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1282,f736])).

fof(f736,plain,(
    ~ r2_hidden(sK16,sK18) ),
    inference(cnf_transformation,[],[f623])).

fof(f623,plain,
    ( sK18 != k4_xboole_0(sK18,k2_tarski(sK16,sK17))
    & ~ r2_hidden(sK17,sK18)
    & ~ r2_hidden(sK16,sK18) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16,sK17,sK18])],[f443,f622])).

fof(f622,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( sK18 != k4_xboole_0(sK18,k2_tarski(sK16,sK17))
      & ~ r2_hidden(sK17,sK18)
      & ~ r2_hidden(sK16,sK18) ) ),
    introduced(choice_axiom,[])).

fof(f443,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f358])).

fof(f358,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f357])).

fof(f357,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f1282,plain,(
    r2_hidden(sK16,sK18) ),
    inference(subsumption_resolution,[],[f1276,f737])).

fof(f737,plain,(
    ~ r2_hidden(sK17,sK18) ),
    inference(cnf_transformation,[],[f623])).

fof(f1276,plain,
    ( r2_hidden(sK17,sK18)
    | r2_hidden(sK16,sK18) ),
    inference(resolution,[],[f1272,f835])).

fof(f835,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f472])).

fof(f472,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f297])).

fof(f297,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l168_zfmisc_1)).

fof(f1272,plain,(
    ~ r1_xboole_0(k2_tarski(sK16,sK17),sK18) ),
    inference(resolution,[],[f1271,f1053])).

fof(f1053,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f580])).

fof(f580,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1271,plain,(
    ~ r1_xboole_0(sK18,k2_tarski(sK16,sK17)) ),
    inference(trivial_inequality_removal,[],[f1267])).

fof(f1267,plain,
    ( sK18 != sK18
    | ~ r1_xboole_0(sK18,k2_tarski(sK16,sK17)) ),
    inference(superposition,[],[f738,f1050])).

fof(f1050,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f733])).

fof(f733,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f153])).

fof(f153,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f738,plain,(
    sK18 != k4_xboole_0(sK18,k2_tarski(sK16,sK17)) ),
    inference(cnf_transformation,[],[f623])).
%------------------------------------------------------------------------------
