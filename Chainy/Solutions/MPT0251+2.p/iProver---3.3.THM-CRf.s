%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0251+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:30 EST 2020

% Result     : Theorem 9.88s
% Output     : CNFRefutation 9.88s
% Verified   : 
% Statistics : Number of formulae       :   30 (  46 expanded)
%              Number of clauses        :    9 (  11 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :   44 (  67 expanded)
%              Number of equality atoms :   28 (  45 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f296,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f469,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f296])).

fof(f1036,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f469])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f858,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f798,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1128,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f858,f798])).

fof(f1381,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k5_xboole_0(k1_tarski(X0),X1),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),X1))) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f1036,f1128])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f855,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f647,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f347,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f348,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f347])).

fof(f500,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f348])).

fof(f641,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k1_tarski(sK35),sK36) != sK36
      & r2_hidden(sK35,sK36) ) ),
    introduced(choice_axiom,[])).

fof(f642,plain,
    ( k2_xboole_0(k1_tarski(sK35),sK36) != sK36
    & r2_hidden(sK35,sK36) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36])],[f500,f641])).

fof(f1124,plain,(
    k2_xboole_0(k1_tarski(sK35),sK36) != sK36 ),
    inference(cnf_transformation,[],[f642])).

fof(f1442,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK35),sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),sK36))) != sK36 ),
    inference(definition_unfolding,[],[f1124,f1128])).

fof(f1123,plain,(
    r2_hidden(sK35,sK36) ),
    inference(cnf_transformation,[],[f642])).

cnf(c_381,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(k5_xboole_0(k1_tarski(X0),X1),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),X1))) = X1 ),
    inference(cnf_transformation,[],[f1381])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f855])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f647])).

cnf(c_8254,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(X1,k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),X1)))) = X1 ),
    inference(theory_normalisation,[status(thm)],[c_381,c_211,c_7])).

cnf(c_18072,plain,
    ( ~ r2_hidden(sK35,sK36)
    | k5_xboole_0(sK36,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),sK36)))) = sK36 ),
    inference(instantiation,[status(thm)],[c_8254])).

cnf(c_468,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),sK36))) != sK36 ),
    inference(cnf_transformation,[],[f1442])).

cnf(c_8221,negated_conjecture,
    ( k5_xboole_0(sK36,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),sK36)))) != sK36 ),
    inference(theory_normalisation,[status(thm)],[c_468,c_211,c_7])).

cnf(c_469,negated_conjecture,
    ( r2_hidden(sK35,sK36) ),
    inference(cnf_transformation,[],[f1123])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18072,c_8221,c_469])).

%------------------------------------------------------------------------------
