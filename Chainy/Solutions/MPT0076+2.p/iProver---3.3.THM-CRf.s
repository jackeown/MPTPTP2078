%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0076+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:18 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   28 (  40 expanded)
%              Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   80 ( 122 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f188,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f110])).

fof(f189,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f188])).

fof(f401,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f189])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f243,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f244,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f243])).

fof(f320,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f244])).

fof(f493,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f320])).

fof(f111,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f112,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ~ ( r1_xboole_0(X1,X0)
            & r1_tarski(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f111])).

fof(f190,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X1,X0)
      & r1_tarski(X1,X0)
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f112])).

fof(f191,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X1,X0)
      & r1_tarski(X1,X0)
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f190])).

fof(f251,plain,
    ( ? [X0,X1] :
        ( r1_xboole_0(X1,X0)
        & r1_tarski(X1,X0)
        & ~ v1_xboole_0(X1) )
   => ( r1_xboole_0(sK16,sK15)
      & r1_tarski(sK16,sK15)
      & ~ v1_xboole_0(sK16) ) ),
    introduced(choice_axiom,[])).

fof(f252,plain,
    ( r1_xboole_0(sK16,sK15)
    & r1_tarski(sK16,sK15)
    & ~ v1_xboole_0(sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16])],[f191,f251])).

fof(f404,plain,(
    r1_xboole_0(sK16,sK15) ),
    inference(cnf_transformation,[],[f252])).

fof(f403,plain,(
    r1_tarski(sK16,sK15) ),
    inference(cnf_transformation,[],[f252])).

fof(f402,plain,(
    ~ v1_xboole_0(sK16) ),
    inference(cnf_transformation,[],[f252])).

cnf(c_145,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X2,X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f401])).

cnf(c_5486,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(sK16,X1)
    | ~ r1_tarski(sK16,X0)
    | v1_xboole_0(sK16) ),
    inference(instantiation,[status(thm)],[c_145])).

cnf(c_5910,plain,
    ( ~ r1_xboole_0(X0,sK15)
    | ~ r1_tarski(sK16,X0)
    | ~ r1_tarski(sK16,sK15)
    | v1_xboole_0(sK16) ),
    inference(instantiation,[status(thm)],[c_5486])).

cnf(c_6133,plain,
    ( ~ r1_xboole_0(sK16,sK15)
    | ~ r1_tarski(sK16,sK15)
    | ~ r1_tarski(sK16,sK16)
    | v1_xboole_0(sK16) ),
    inference(instantiation,[status(thm)],[c_5910])).

cnf(c_65,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f493])).

cnf(c_5875,plain,
    ( r1_tarski(sK16,sK16) ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_146,negated_conjecture,
    ( r1_xboole_0(sK16,sK15) ),
    inference(cnf_transformation,[],[f404])).

cnf(c_147,negated_conjecture,
    ( r1_tarski(sK16,sK15) ),
    inference(cnf_transformation,[],[f403])).

cnf(c_148,negated_conjecture,
    ( ~ v1_xboole_0(sK16) ),
    inference(cnf_transformation,[],[f402])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6133,c_5875,c_146,c_147,c_148])).

%------------------------------------------------------------------------------
