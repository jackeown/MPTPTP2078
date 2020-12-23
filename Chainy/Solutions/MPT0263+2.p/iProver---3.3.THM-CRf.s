%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0263+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:31 EST 2020

% Result     : Theorem 9.73s
% Output     : CNFRefutation 9.73s
% Verified   : 
% Statistics : Number of formulae       :   29 (  36 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   54 (  68 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f338,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f656,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f338])).

fof(f1122,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f656])).

fof(f86,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f416,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f86])).

fof(f797,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f416])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f822,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1249,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f797,f822])).

fof(f357,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f522,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f357])).

fof(f1157,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f522])).

fof(f359,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f360,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f359])).

fof(f524,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f360])).

fof(f665,plain,
    ( ? [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k3_xboole_0(k1_tarski(sK35),sK36) != k1_tarski(sK35)
      & ~ r1_xboole_0(k1_tarski(sK35),sK36) ) ),
    introduced(choice_axiom,[])).

fof(f666,plain,
    ( k3_xboole_0(k1_tarski(sK35),sK36) != k1_tarski(sK35)
    & ~ r1_xboole_0(k1_tarski(sK35),sK36) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36])],[f524,f665])).

fof(f1160,plain,(
    k3_xboole_0(k1_tarski(sK35),sK36) != k1_tarski(sK35) ),
    inference(cnf_transformation,[],[f666])).

fof(f1488,plain,(
    k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),sK36)) != k1_tarski(sK35) ),
    inference(definition_unfolding,[],[f1160,f822])).

fof(f1159,plain,(
    ~ r1_xboole_0(k1_tarski(sK35),sK36) ),
    inference(cnf_transformation,[],[f666])).

cnf(c_442,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f1122])).

cnf(c_20197,plain,
    ( r1_tarski(k1_tarski(sK35),sK36)
    | ~ r2_hidden(sK35,sK36) ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_130,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f1249])).

cnf(c_17342,plain,
    ( ~ r1_tarski(k1_tarski(sK35),sK36)
    | k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),sK36)) = k1_tarski(sK35) ),
    inference(instantiation,[status(thm)],[c_130])).

cnf(c_478,plain,
    ( r1_xboole_0(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f1157])).

cnf(c_17135,plain,
    ( r1_xboole_0(k1_tarski(sK35),sK36)
    | r2_hidden(sK35,sK36) ),
    inference(instantiation,[status(thm)],[c_478])).

cnf(c_480,negated_conjecture,
    ( k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),sK36)) != k1_tarski(sK35) ),
    inference(cnf_transformation,[],[f1488])).

cnf(c_481,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(sK35),sK36) ),
    inference(cnf_transformation,[],[f1159])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20197,c_17342,c_17135,c_480,c_481])).

%------------------------------------------------------------------------------
