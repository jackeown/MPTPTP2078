%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0250+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:49 EST 2020

% Result     : Theorem 0.59s
% Output     : CNFRefutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   15 (  20 expanded)
%              Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    7
%              Number of atoms          :   26 (  38 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f6,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK0,sK1)
      & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,
    ( ~ r2_hidden(sK0,sK1)
    & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f6])).

fof(f10,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f9,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f7])).

cnf(c_0,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_1,negated_conjecture,
    ( ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_30,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_2,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30,c_2])).


%------------------------------------------------------------------------------
