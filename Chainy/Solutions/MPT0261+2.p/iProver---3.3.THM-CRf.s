%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0261+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:31 EST 2020

% Result     : Theorem 7.79s
% Output     : CNFRefutation 7.79s
% Verified   : 
% Statistics : Number of formulae       :   15 (  20 expanded)
%              Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  39 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f298,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f481,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f298])).

fof(f1058,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f481])).

fof(f357,conjecture,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f358,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
       => r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f357])).

fof(f520,plain,(
    ? [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      & ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f358])).

fof(f661,plain,
    ( ? [X0,X1] :
        ( ~ r1_xboole_0(k1_tarski(X0),X1)
        & ~ r2_hidden(X0,X1) )
   => ( ~ r1_xboole_0(k1_tarski(sK35),sK36)
      & ~ r2_hidden(sK35,sK36) ) ),
    introduced(choice_axiom,[])).

fof(f662,plain,
    ( ~ r1_xboole_0(k1_tarski(sK35),sK36)
    & ~ r2_hidden(sK35,sK36) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36])],[f520,f661])).

fof(f1154,plain,(
    ~ r1_xboole_0(k1_tarski(sK35),sK36) ),
    inference(cnf_transformation,[],[f662])).

fof(f1153,plain,(
    ~ r2_hidden(sK35,sK36) ),
    inference(cnf_transformation,[],[f662])).

cnf(c_383,plain,
    ( r1_xboole_0(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f1058])).

cnf(c_14894,plain,
    ( r1_xboole_0(k1_tarski(sK35),sK36)
    | r2_hidden(sK35,sK36) ),
    inference(instantiation,[status(thm)],[c_383])).

cnf(c_478,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(sK35),sK36) ),
    inference(cnf_transformation,[],[f1154])).

cnf(c_479,negated_conjecture,
    ( ~ r2_hidden(sK35,sK36) ),
    inference(cnf_transformation,[],[f1153])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14894,c_478,c_479])).

%------------------------------------------------------------------------------
