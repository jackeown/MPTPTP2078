%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0270+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:32 EST 2020

% Result     : Theorem 7.72s
% Output     : CNFRefutation 7.72s
% Verified   : 
% Statistics : Number of formulae       :   22 (  38 expanded)
%              Number of clauses        :   10 (  11 expanded)
%              Number of leaves         :    3 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   55 ( 109 expanded)
%              Number of equality atoms :   30 (  57 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f302,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f653,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f302])).

fof(f1082,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f653])).

fof(f1083,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f653])).

fof(f366,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f367,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f366])).

fof(f536,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f367])).

fof(f680,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) )
      & ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f536])).

fof(f681,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) )
        & ( ~ r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) ) )
   => ( ( r2_hidden(sK35,sK36)
        | k4_xboole_0(k1_tarski(sK35),sK36) != k1_tarski(sK35) )
      & ( ~ r2_hidden(sK35,sK36)
        | k4_xboole_0(k1_tarski(sK35),sK36) = k1_tarski(sK35) ) ) ),
    introduced(choice_axiom,[])).

fof(f682,plain,
    ( ( r2_hidden(sK35,sK36)
      | k4_xboole_0(k1_tarski(sK35),sK36) != k1_tarski(sK35) )
    & ( ~ r2_hidden(sK35,sK36)
      | k4_xboole_0(k1_tarski(sK35),sK36) = k1_tarski(sK35) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36])],[f680,f681])).

fof(f1187,plain,
    ( r2_hidden(sK35,sK36)
    | k4_xboole_0(k1_tarski(sK35),sK36) != k1_tarski(sK35) ),
    inference(cnf_transformation,[],[f682])).

fof(f1186,plain,
    ( ~ r2_hidden(sK35,sK36)
    | k4_xboole_0(k1_tarski(sK35),sK36) = k1_tarski(sK35) ),
    inference(cnf_transformation,[],[f682])).

cnf(c_388,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1082])).

cnf(c_15506,plain,
    ( ~ r2_hidden(sK35,sK36)
    | k4_xboole_0(k1_tarski(sK35),sK36) != k1_tarski(sK35) ),
    inference(instantiation,[status(thm)],[c_388])).

cnf(c_387,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1083])).

cnf(c_15470,plain,
    ( r2_hidden(sK35,sK36)
    | k4_xboole_0(k1_tarski(sK35),sK36) = k1_tarski(sK35) ),
    inference(instantiation,[status(thm)],[c_387])).

cnf(c_15471,plain,
    ( k4_xboole_0(k1_tarski(sK35),sK36) = k1_tarski(sK35)
    | r2_hidden(sK35,sK36) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15470])).

cnf(c_491,negated_conjecture,
    ( r2_hidden(sK35,sK36)
    | k4_xboole_0(k1_tarski(sK35),sK36) != k1_tarski(sK35) ),
    inference(cnf_transformation,[],[f1187])).

cnf(c_497,plain,
    ( k4_xboole_0(k1_tarski(sK35),sK36) != k1_tarski(sK35)
    | r2_hidden(sK35,sK36) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_492,negated_conjecture,
    ( ~ r2_hidden(sK35,sK36)
    | k4_xboole_0(k1_tarski(sK35),sK36) = k1_tarski(sK35) ),
    inference(cnf_transformation,[],[f1186])).

cnf(c_496,plain,
    ( k4_xboole_0(k1_tarski(sK35),sK36) = k1_tarski(sK35)
    | r2_hidden(sK35,sK36) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_492])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15506,c_15471,c_497,c_491,c_496])).

%------------------------------------------------------------------------------
