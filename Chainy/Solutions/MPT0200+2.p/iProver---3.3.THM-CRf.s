%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0200+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:27 EST 2020

% Result     : Theorem 7.60s
% Output     : CNFRefutation 7.60s
% Verified   : 
% Statistics : Number of formulae       :   33 (  90 expanded)
%              Number of clauses        :    8 (  10 expanded)
%              Number of leaves         :    9 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :   34 (  91 expanded)
%              Number of equality atoms :   33 (  90 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :   14 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f462,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f614,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f795,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f462,f614,f614])).

fof(f209,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f210,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(negated_conjecture,[],[f209])).

fof(f382,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0) ),
    inference(ennf_transformation,[],[f210])).

fof(f457,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0)
   => k2_enumset1(sK18,sK19,sK20,sK21) != k2_enumset1(sK21,sK20,sK19,sK18) ),
    introduced(choice_axiom,[])).

fof(f458,plain,(
    k2_enumset1(sK18,sK19,sK20,sK21) != k2_enumset1(sK21,sK20,sK19,sK18) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18,sK19,sK20,sK21])],[f382,f457])).

fof(f724,plain,(
    k2_enumset1(sK18,sK19,sK20,sK21) != k2_enumset1(sK21,sK20,sK19,sK18) ),
    inference(cnf_transformation,[],[f458])).

fof(f187,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f702,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f187])).

fof(f211,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f725,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f211])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f674,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f783,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f674,f614])).

fof(f784,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f725,f783])).

fof(f786,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f702,f783,f784,f784])).

fof(f962,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k1_tarski(sK20)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK18))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k1_tarski(sK20)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k1_tarski(sK20)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK18))))))) ),
    inference(definition_unfolding,[],[f724,f786,f786])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f671,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f463,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f795])).

cnf(c_258,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k1_tarski(sK20)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK18))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k1_tarski(sK20)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k1_tarski(sK20)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK18))))))) ),
    inference(cnf_transformation,[],[f962])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f671])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f463])).

cnf(c_4012,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK18))),k5_xboole_0(k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k1_tarski(sK20))),k4_xboole_0(k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k1_tarski(sK20))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k1_tarski(sK20))))),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK18))))))))))))) != k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19))),k5_xboole_0(k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19))))),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))))))))) ),
    inference(theory_normalisation,[status(thm)],[c_258,c_211,c_7])).

cnf(c_8473,plain,
    ( k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK18))),k5_xboole_0(k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))),k4_xboole_0(k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK18))))))))))))) != k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19))),k5_xboole_0(k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19))))),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))))))))) ),
    inference(superposition,[status(thm)],[c_6,c_4012])).

cnf(c_8954,plain,
    ( k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK18))),k5_xboole_0(k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK18))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK18))))),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))))))))) != k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19))),k5_xboole_0(k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19))))),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))))))))) ),
    inference(superposition,[status(thm)],[c_6,c_8473])).

cnf(c_9589,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_6,c_8954])).

%------------------------------------------------------------------------------
