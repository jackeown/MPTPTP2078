%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0256+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:30 EST 2020

% Result     : Theorem 7.77s
% Output     : CNFRefutation 7.77s
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
fof(f299,axiom,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1)
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f477,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1) ) ),
    inference(ennf_transformation,[],[f299])).

fof(f1048,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f477])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f807,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1396,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(X1))) != k1_tarski(X1) ) ),
    inference(definition_unfolding,[],[f1048,f807])).

fof(f352,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1)
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f353,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1)
       => r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f352])).

fof(f509,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      & k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1) ) ),
    inference(ennf_transformation,[],[f353])).

fof(f650,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        & k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1) )
   => ( ~ r2_hidden(sK36,sK35)
      & k3_xboole_0(sK35,k1_tarski(sK36)) = k1_tarski(sK36) ) ),
    introduced(choice_axiom,[])).

fof(f651,plain,
    ( ~ r2_hidden(sK36,sK35)
    & k3_xboole_0(sK35,k1_tarski(sK36)) = k1_tarski(sK36) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36])],[f509,f650])).

fof(f1138,plain,(
    ~ r2_hidden(sK36,sK35) ),
    inference(cnf_transformation,[],[f651])).

fof(f1137,plain,(
    k3_xboole_0(sK35,k1_tarski(sK36)) = k1_tarski(sK36) ),
    inference(cnf_transformation,[],[f651])).

fof(f1461,plain,(
    k4_xboole_0(sK35,k4_xboole_0(sK35,k1_tarski(sK36))) = k1_tarski(sK36) ),
    inference(definition_unfolding,[],[f1137,f807])).

cnf(c_384,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1396])).

cnf(c_14712,plain,
    ( r2_hidden(sK36,sK35)
    | k4_xboole_0(sK35,k4_xboole_0(sK35,k1_tarski(sK36))) != k1_tarski(sK36) ),
    inference(instantiation,[status(thm)],[c_384])).

cnf(c_473,negated_conjecture,
    ( ~ r2_hidden(sK36,sK35) ),
    inference(cnf_transformation,[],[f1138])).

cnf(c_474,negated_conjecture,
    ( k4_xboole_0(sK35,k4_xboole_0(sK35,k1_tarski(sK36))) = k1_tarski(sK36) ),
    inference(cnf_transformation,[],[f1461])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14712,c_473,c_474])).

%------------------------------------------------------------------------------
