%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0115+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:22 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   24 (  29 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 (  56 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f85,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f214,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f85])).

fof(f462,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f214])).

fof(f54,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f191,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f54])).

fof(f424,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f191])).

fof(f56,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f56])).

fof(f192,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f57])).

fof(f325,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_xboole_0(X0,X2),X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_xboole_0(sK13,sK15),sK14)
      & r1_tarski(sK13,sK14) ) ),
    introduced(choice_axiom,[])).

fof(f326,plain,
    ( ~ r1_tarski(k3_xboole_0(sK13,sK15),sK14)
    & r1_tarski(sK13,sK14) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15])],[f192,f325])).

fof(f430,plain,(
    ~ r1_tarski(k3_xboole_0(sK13,sK15),sK14) ),
    inference(cnf_transformation,[],[f326])).

fof(f102,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f480,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f102])).

fof(f591,plain,(
    ~ r1_tarski(k4_xboole_0(sK13,k4_xboole_0(sK13,sK15)),sK14) ),
    inference(definition_unfolding,[],[f430,f480])).

fof(f429,plain,(
    r1_tarski(sK13,sK14) ),
    inference(cnf_transformation,[],[f326])).

cnf(c_128,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f462])).

cnf(c_8970,plain,
    ( r1_tarski(k4_xboole_0(sK13,k4_xboole_0(sK13,sK15)),k4_xboole_0(sK14,k4_xboole_0(sK13,sK15)))
    | ~ r1_tarski(sK13,sK14) ),
    inference(instantiation,[status(thm)],[c_128])).

cnf(c_91,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f424])).

cnf(c_7584,plain,
    ( ~ r1_tarski(k4_xboole_0(sK13,k4_xboole_0(sK13,sK15)),k4_xboole_0(sK14,X0))
    | r1_tarski(k4_xboole_0(sK13,k4_xboole_0(sK13,sK15)),sK14) ),
    inference(instantiation,[status(thm)],[c_91])).

cnf(c_8969,plain,
    ( ~ r1_tarski(k4_xboole_0(sK13,k4_xboole_0(sK13,sK15)),k4_xboole_0(sK14,k4_xboole_0(sK13,sK15)))
    | r1_tarski(k4_xboole_0(sK13,k4_xboole_0(sK13,sK15)),sK14) ),
    inference(instantiation,[status(thm)],[c_7584])).

cnf(c_95,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(sK13,k4_xboole_0(sK13,sK15)),sK14) ),
    inference(cnf_transformation,[],[f591])).

cnf(c_96,negated_conjecture,
    ( r1_tarski(sK13,sK14) ),
    inference(cnf_transformation,[],[f429])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8970,c_8969,c_95,c_96])).

%------------------------------------------------------------------------------
