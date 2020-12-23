%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0259+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:31 EST 2020

% Result     : Theorem 7.87s
% Output     : CNFRefutation 7.87s
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
fof(f297,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f478,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f297])).

fof(f1053,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f478])).

fof(f355,conjecture,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f356,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( r2_hidden(X0,X1)
          & r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f355])).

fof(f516,plain,(
    ? [X0,X1] :
      ( r2_hidden(X0,X1)
      & r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f356])).

fof(f657,plain,
    ( ? [X0,X1] :
        ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) )
   => ( r2_hidden(sK35,sK36)
      & r1_xboole_0(k1_tarski(sK35),sK36) ) ),
    introduced(choice_axiom,[])).

fof(f658,plain,
    ( r2_hidden(sK35,sK36)
    & r1_xboole_0(k1_tarski(sK35),sK36) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36])],[f516,f657])).

fof(f1148,plain,(
    r2_hidden(sK35,sK36) ),
    inference(cnf_transformation,[],[f658])).

fof(f1147,plain,(
    r1_xboole_0(k1_tarski(sK35),sK36) ),
    inference(cnf_transformation,[],[f658])).

cnf(c_382,plain,
    ( ~ r1_xboole_0(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f1053])).

cnf(c_14793,plain,
    ( ~ r1_xboole_0(k1_tarski(sK35),sK36)
    | ~ r2_hidden(sK35,sK36) ),
    inference(instantiation,[status(thm)],[c_382])).

cnf(c_476,negated_conjecture,
    ( r2_hidden(sK35,sK36) ),
    inference(cnf_transformation,[],[f1148])).

cnf(c_477,negated_conjecture,
    ( r1_xboole_0(k1_tarski(sK35),sK36) ),
    inference(cnf_transformation,[],[f1147])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14793,c_476,c_477])).

%------------------------------------------------------------------------------
