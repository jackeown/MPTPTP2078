%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0064+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:16 EST 2020

% Result     : Theorem 1.33s
% Output     : CNFRefutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   15 (  20 expanded)
%              Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  39 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f225,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f114])).

fof(f98,conjecture,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f99,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( r2_xboole_0(X1,X0)
          & r2_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f98])).

fof(f162,plain,(
    ? [X0,X1] :
      ( r2_xboole_0(X1,X0)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f99])).

fof(f222,plain,
    ( ? [X0,X1] :
        ( r2_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) )
   => ( r2_xboole_0(sK16,sK15)
      & r2_xboole_0(sK15,sK16) ) ),
    introduced(choice_axiom,[])).

fof(f223,plain,
    ( r2_xboole_0(sK16,sK15)
    & r2_xboole_0(sK15,sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16])],[f162,f222])).

fof(f360,plain,(
    r2_xboole_0(sK16,sK15) ),
    inference(cnf_transformation,[],[f223])).

fof(f359,plain,(
    r2_xboole_0(sK15,sK16) ),
    inference(cnf_transformation,[],[f223])).

cnf(c_1,plain,
    ( ~ r2_xboole_0(X0,X1)
    | ~ r2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f225])).

cnf(c_4888,plain,
    ( ~ r2_xboole_0(sK15,sK16)
    | ~ r2_xboole_0(sK16,sK15) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_132,negated_conjecture,
    ( r2_xboole_0(sK16,sK15) ),
    inference(cnf_transformation,[],[f360])).

cnf(c_133,negated_conjecture,
    ( r2_xboole_0(sK15,sK16) ),
    inference(cnf_transformation,[],[f359])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4888,c_132,c_133])).

%------------------------------------------------------------------------------
