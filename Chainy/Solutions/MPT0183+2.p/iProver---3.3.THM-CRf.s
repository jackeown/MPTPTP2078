%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0183+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:26 EST 2020

% Result     : Theorem 7.47s
% Output     : CNFRefutation 7.47s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 100 expanded)
%              Number of clauses        :    9 (  11 expanded)
%              Number of leaves         :   10 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   38 ( 101 expanded)
%              Number of equality atoms :   37 ( 100 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :   12 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f249,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f744,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f249])).

fof(f193,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f688,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f193])).

fof(f192,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f687,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f192])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f655,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f595,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f745,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f655,f595])).

fof(f746,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f687,f745])).

fof(f747,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f688,f745,f746])).

fof(f960,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2))))))) ),
    inference(definition_unfolding,[],[f744,f747,f747])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f652,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f444,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f443,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f757,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f443,f595,f595])).

fof(f190,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f191,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(negated_conjecture,[],[f190])).

fof(f363,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X2,X0) ),
    inference(ennf_transformation,[],[f191])).

fof(f438,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X2,X0)
   => k1_enumset1(sK18,sK19,sK20) != k1_enumset1(sK19,sK20,sK18) ),
    introduced(choice_axiom,[])).

fof(f439,plain,(
    k1_enumset1(sK18,sK19,sK20) != k1_enumset1(sK19,sK20,sK18) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18,sK19,sK20])],[f363,f438])).

fof(f686,plain,(
    k1_enumset1(sK18,sK19,sK20) != k1_enumset1(sK19,sK20,sK18) ),
    inference(cnf_transformation,[],[f439])).

fof(f905,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK18))))),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK18))))))) ),
    inference(definition_unfolding,[],[f686,f747,f747])).

cnf(c_294,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2))))))) ),
    inference(cnf_transformation,[],[f960])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f652])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f444])).

cnf(c_3909,plain,
    ( k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2))),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2))))))))))) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))))))) ),
    inference(theory_normalisation,[status(thm)],[c_294,c_211,c_7])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f757])).

cnf(c_239,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK18))))),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK18))))))) ),
    inference(cnf_transformation,[],[f905])).

cnf(c_3959,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK18))),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK18))))))))))) != k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))))))) ),
    inference(theory_normalisation,[status(thm)],[c_239,c_211,c_7])).

cnf(c_8360,plain,
    ( k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK20))),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK20))))))))))) != k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))))))) ),
    inference(superposition,[status(thm)],[c_6,c_3959])).

cnf(c_8835,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_3909,c_8360])).

%------------------------------------------------------------------------------
