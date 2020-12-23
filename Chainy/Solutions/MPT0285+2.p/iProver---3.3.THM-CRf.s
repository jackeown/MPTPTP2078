%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0285+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:33 EST 2020

% Result     : Theorem 12.02s
% Output     : CNFRefutation 12.02s
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
fof(f308,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f512,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f308])).

fof(f1128,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f512])).

fof(f383,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f384,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f383])).

fof(f557,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(X1))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f384])).

fof(f709,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k3_tarski(X1))
        & r2_hidden(X0,X1) )
   => ( ~ r1_tarski(sK35,k3_tarski(sK36))
      & r2_hidden(sK35,sK36) ) ),
    introduced(choice_axiom,[])).

fof(f710,plain,
    ( ~ r1_tarski(sK35,k3_tarski(sK36))
    & r2_hidden(sK35,sK36) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36])],[f557,f709])).

fof(f1245,plain,(
    ~ r1_tarski(sK35,k3_tarski(sK36)) ),
    inference(cnf_transformation,[],[f710])).

fof(f1244,plain,(
    r2_hidden(sK35,sK36) ),
    inference(cnf_transformation,[],[f710])).

cnf(c_405,plain,
    ( r1_tarski(X0,k3_tarski(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f1128])).

cnf(c_16459,plain,
    ( r1_tarski(sK35,k3_tarski(sK36))
    | ~ r2_hidden(sK35,sK36) ),
    inference(instantiation,[status(thm)],[c_405])).

cnf(c_521,negated_conjecture,
    ( ~ r1_tarski(sK35,k3_tarski(sK36)) ),
    inference(cnf_transformation,[],[f1245])).

cnf(c_522,negated_conjecture,
    ( r2_hidden(sK35,sK36) ),
    inference(cnf_transformation,[],[f1244])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16459,c_521,c_522])).

%------------------------------------------------------------------------------
