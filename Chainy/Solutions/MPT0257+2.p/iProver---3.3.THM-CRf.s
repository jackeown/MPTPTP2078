%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0257+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:31 EST 2020

% Result     : Theorem 7.88s
% Output     : CNFRefutation 7.88s
% Verified   : 
% Statistics : Number of formulae       :   19 (  26 expanded)
%              Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   32 (  46 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f301,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f481,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f301])).

fof(f1052,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f481])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f809,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1400,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f1052,f809])).

fof(f353,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f354,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f353])).

fof(f511,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) != k1_tarski(X0)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f354])).

fof(f652,plain,
    ( ? [X0,X1] :
        ( k3_xboole_0(X1,k1_tarski(X0)) != k1_tarski(X0)
        & r2_hidden(X0,X1) )
   => ( k3_xboole_0(sK36,k1_tarski(sK35)) != k1_tarski(sK35)
      & r2_hidden(sK35,sK36) ) ),
    introduced(choice_axiom,[])).

fof(f653,plain,
    ( k3_xboole_0(sK36,k1_tarski(sK35)) != k1_tarski(sK35)
    & r2_hidden(sK35,sK36) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36])],[f511,f652])).

fof(f1141,plain,(
    k3_xboole_0(sK36,k1_tarski(sK35)) != k1_tarski(sK35) ),
    inference(cnf_transformation,[],[f653])).

fof(f1465,plain,(
    k4_xboole_0(sK36,k4_xboole_0(sK36,k1_tarski(sK35))) != k1_tarski(sK35) ),
    inference(definition_unfolding,[],[f1141,f809])).

fof(f1140,plain,(
    r2_hidden(sK35,sK36) ),
    inference(cnf_transformation,[],[f653])).

cnf(c_386,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1400])).

cnf(c_14034,plain,
    ( ~ r2_hidden(sK35,sK36)
    | k4_xboole_0(sK36,k4_xboole_0(sK36,k1_tarski(sK35))) = k1_tarski(sK35) ),
    inference(instantiation,[status(thm)],[c_386])).

cnf(c_474,negated_conjecture,
    ( k4_xboole_0(sK36,k4_xboole_0(sK36,k1_tarski(sK35))) != k1_tarski(sK35) ),
    inference(cnf_transformation,[],[f1465])).

cnf(c_475,negated_conjecture,
    ( r2_hidden(sK35,sK36) ),
    inference(cnf_transformation,[],[f1140])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14034,c_474,c_475])).

%------------------------------------------------------------------------------
