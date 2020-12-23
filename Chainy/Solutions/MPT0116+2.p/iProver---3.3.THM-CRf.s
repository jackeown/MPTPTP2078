%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0116+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:22 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   21 (  26 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   41 (  53 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f86,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f216,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f86])).

fof(f465,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f216])).

fof(f54,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f192,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f54])).

fof(f426,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f192])).

fof(f57,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f57])).

fof(f194,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k4_xboole_0(X0,X2),X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f58])).

fof(f327,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k4_xboole_0(X0,X2),X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k4_xboole_0(sK13,sK15),sK14)
      & r1_tarski(sK13,sK14) ) ),
    introduced(choice_axiom,[])).

fof(f328,plain,
    ( ~ r1_tarski(k4_xboole_0(sK13,sK15),sK14)
    & r1_tarski(sK13,sK14) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15])],[f194,f327])).

fof(f433,plain,(
    ~ r1_tarski(k4_xboole_0(sK13,sK15),sK14) ),
    inference(cnf_transformation,[],[f328])).

fof(f432,plain,(
    r1_tarski(sK13,sK14) ),
    inference(cnf_transformation,[],[f328])).

cnf(c_129,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f465])).

cnf(c_9005,plain,
    ( r1_tarski(k4_xboole_0(sK13,sK15),k4_xboole_0(sK14,sK15))
    | ~ r1_tarski(sK13,sK14) ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_91,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f426])).

cnf(c_7628,plain,
    ( ~ r1_tarski(k4_xboole_0(sK13,sK15),k4_xboole_0(sK14,X0))
    | r1_tarski(k4_xboole_0(sK13,sK15),sK14) ),
    inference(instantiation,[status(thm)],[c_91])).

cnf(c_9004,plain,
    ( ~ r1_tarski(k4_xboole_0(sK13,sK15),k4_xboole_0(sK14,sK15))
    | r1_tarski(k4_xboole_0(sK13,sK15),sK14) ),
    inference(instantiation,[status(thm)],[c_7628])).

cnf(c_96,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(sK13,sK15),sK14) ),
    inference(cnf_transformation,[],[f433])).

cnf(c_97,negated_conjecture,
    ( r1_tarski(sK13,sK14) ),
    inference(cnf_transformation,[],[f432])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9005,c_9004,c_96,c_97])).

%------------------------------------------------------------------------------
