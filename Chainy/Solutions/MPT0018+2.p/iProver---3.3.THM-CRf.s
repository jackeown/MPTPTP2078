%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0018+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:11 EST 2020

% Result     : Theorem 1.46s
% Output     : CNFRefutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   21 (  26 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  54 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f52,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f218,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f44,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f81])).

fof(f210,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f41,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(X0,X1),X2)
       => r1_tarski(X0,X2) ) ),
    inference(negated_conjecture,[],[f41])).

fof(f80,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X2)
      & r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f135,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X2)
        & r1_tarski(k2_xboole_0(X0,X1),X2) )
   => ( ~ r1_tarski(sK13,sK15)
      & r1_tarski(k2_xboole_0(sK13,sK14),sK15) ) ),
    introduced(choice_axiom,[])).

fof(f136,plain,
    ( ~ r1_tarski(sK13,sK15)
    & r1_tarski(k2_xboole_0(sK13,sK14),sK15) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15])],[f80,f135])).

fof(f208,plain,(
    ~ r1_tarski(sK13,sK15) ),
    inference(cnf_transformation,[],[f136])).

fof(f207,plain,(
    r1_tarski(k2_xboole_0(sK13,sK14),sK15) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_79,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f218])).

cnf(c_3546,plain,
    ( r1_tarski(sK13,k2_xboole_0(sK13,sK14)) ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(c_71,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f210])).

cnf(c_3233,plain,
    ( ~ r1_tarski(X0,sK15)
    | ~ r1_tarski(sK13,X0)
    | r1_tarski(sK13,sK15) ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_3455,plain,
    ( ~ r1_tarski(k2_xboole_0(sK13,sK14),sK15)
    | ~ r1_tarski(sK13,k2_xboole_0(sK13,sK14))
    | r1_tarski(sK13,sK15) ),
    inference(instantiation,[status(thm)],[c_3233])).

cnf(c_68,negated_conjecture,
    ( ~ r1_tarski(sK13,sK15) ),
    inference(cnf_transformation,[],[f208])).

cnf(c_69,negated_conjecture,
    ( r1_tarski(k2_xboole_0(sK13,sK14),sK15) ),
    inference(cnf_transformation,[],[f207])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3546,c_3455,c_68,c_69])).

%------------------------------------------------------------------------------
