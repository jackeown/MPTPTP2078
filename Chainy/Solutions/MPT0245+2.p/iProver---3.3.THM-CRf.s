%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0245+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:30 EST 2020

% Result     : Theorem 7.50s
% Output     : CNFRefutation 7.50s
% Verified   : 
% Statistics : Number of formulae       :   19 (  31 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    3 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   46 (  88 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f300,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f466,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f300])).

fof(f467,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f466])).

fof(f1020,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f467])).

fof(f340,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f341,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
          | r2_hidden(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f340])).

fof(f485,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      & ~ r2_hidden(X2,X0)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f341])).

fof(f486,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      & ~ r2_hidden(X2,X0)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f485])).

fof(f621,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
        & ~ r2_hidden(X2,X0)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(sK33,k4_xboole_0(sK34,k1_tarski(sK35)))
      & ~ r2_hidden(sK35,sK33)
      & r1_tarski(sK33,sK34) ) ),
    introduced(choice_axiom,[])).

fof(f622,plain,
    ( ~ r1_tarski(sK33,k4_xboole_0(sK34,k1_tarski(sK35)))
    & ~ r2_hidden(sK35,sK33)
    & r1_tarski(sK33,sK34) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK33,sK34,sK35])],[f486,f621])).

fof(f1085,plain,(
    ~ r1_tarski(sK33,k4_xboole_0(sK34,k1_tarski(sK35))) ),
    inference(cnf_transformation,[],[f622])).

fof(f1084,plain,(
    ~ r2_hidden(sK35,sK33) ),
    inference(cnf_transformation,[],[f622])).

fof(f1083,plain,(
    r1_tarski(sK33,sK34) ),
    inference(cnf_transformation,[],[f622])).

cnf(c_385,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
    | r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f1020])).

cnf(c_16123,plain,
    ( r1_tarski(sK33,k4_xboole_0(sK34,k1_tarski(sK35)))
    | ~ r1_tarski(sK33,sK34)
    | r2_hidden(sK35,sK33) ),
    inference(instantiation,[status(thm)],[c_385])).

cnf(c_448,negated_conjecture,
    ( ~ r1_tarski(sK33,k4_xboole_0(sK34,k1_tarski(sK35))) ),
    inference(cnf_transformation,[],[f1085])).

cnf(c_449,negated_conjecture,
    ( ~ r2_hidden(sK35,sK33) ),
    inference(cnf_transformation,[],[f1084])).

cnf(c_450,negated_conjecture,
    ( r1_tarski(sK33,sK34) ),
    inference(cnf_transformation,[],[f1083])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16123,c_448,c_449,c_450])).

%------------------------------------------------------------------------------
