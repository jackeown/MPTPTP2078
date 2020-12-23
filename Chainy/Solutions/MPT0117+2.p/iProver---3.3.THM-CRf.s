%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0117+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:22 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   26 (  42 expanded)
%              Number of clauses        :   10 (  11 expanded)
%              Number of leaves         :    4 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   60 ( 110 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f195,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f57])).

fof(f435,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f195])).

fof(f163,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k4_xboole_0(X1,X0),X2)
        & r1_tarski(k4_xboole_0(X0,X1),X2) )
     => r1_tarski(k5_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f273,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X1),X2)
      | ~ r1_tarski(k4_xboole_0(X1,X0),X2)
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f163])).

fof(f274,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X1),X2)
      | ~ r1_tarski(k4_xboole_0(X1,X0),X2)
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(flattening,[],[f273])).

fof(f551,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X1),X2)
      | ~ r1_tarski(k4_xboole_0(X1,X0),X2)
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f274])).

fof(f59,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X2,X1)
          & r1_tarski(X0,X1) )
       => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f59])).

fof(f197,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f60])).

fof(f198,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f197])).

fof(f330,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k5_xboole_0(sK13,sK15),sK14)
      & r1_tarski(sK15,sK14)
      & r1_tarski(sK13,sK14) ) ),
    introduced(choice_axiom,[])).

fof(f331,plain,
    ( ~ r1_tarski(k5_xboole_0(sK13,sK15),sK14)
    & r1_tarski(sK15,sK14)
    & r1_tarski(sK13,sK14) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15])],[f198,f330])).

fof(f439,plain,(
    ~ r1_tarski(k5_xboole_0(sK13,sK15),sK14) ),
    inference(cnf_transformation,[],[f331])).

fof(f438,plain,(
    r1_tarski(sK15,sK14) ),
    inference(cnf_transformation,[],[f331])).

fof(f437,plain,(
    r1_tarski(sK13,sK14) ),
    inference(cnf_transformation,[],[f331])).

cnf(c_96,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f435])).

cnf(c_9244,plain,
    ( ~ r1_tarski(X0,sK14)
    | r1_tarski(k4_xboole_0(X0,X1),sK14) ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(c_12672,plain,
    ( r1_tarski(k4_xboole_0(sK13,sK15),sK14)
    | ~ r1_tarski(sK13,sK14) ),
    inference(instantiation,[status(thm)],[c_9244])).

cnf(c_8921,plain,
    ( r1_tarski(k4_xboole_0(sK15,sK13),sK14)
    | ~ r1_tarski(sK15,sK14) ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(c_210,plain,
    ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
    | ~ r1_tarski(k4_xboole_0(X1,X0),X2)
    | r1_tarski(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f551])).

cnf(c_7833,plain,
    ( ~ r1_tarski(k4_xboole_0(sK15,sK13),sK14)
    | ~ r1_tarski(k4_xboole_0(sK13,sK15),sK14)
    | r1_tarski(k5_xboole_0(sK13,sK15),sK14) ),
    inference(instantiation,[status(thm)],[c_210])).

cnf(c_98,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(sK13,sK15),sK14) ),
    inference(cnf_transformation,[],[f439])).

cnf(c_99,negated_conjecture,
    ( r1_tarski(sK15,sK14) ),
    inference(cnf_transformation,[],[f438])).

cnf(c_100,negated_conjecture,
    ( r1_tarski(sK13,sK14) ),
    inference(cnf_transformation,[],[f437])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12672,c_8921,c_7833,c_98,c_99,c_100])).

%------------------------------------------------------------------------------
