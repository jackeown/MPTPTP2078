%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0197+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:27 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :   31 (  72 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    9 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   32 (  73 expanded)
%              Number of equality atoms :   31 (  72 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :   14 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f459,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f611,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f789,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f459,f611,f611])).

fof(f206,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f207,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X0,X1) ),
    inference(negated_conjecture,[],[f206])).

fof(f379,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X3,X0,X1) ),
    inference(ennf_transformation,[],[f207])).

fof(f454,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X3,X0,X1)
   => k2_enumset1(sK18,sK19,sK20,sK21) != k2_enumset1(sK20,sK21,sK18,sK19) ),
    introduced(choice_axiom,[])).

fof(f455,plain,(
    k2_enumset1(sK18,sK19,sK20,sK21) != k2_enumset1(sK20,sK21,sK18,sK19) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18,sK19,sK20,sK21])],[f379,f454])).

fof(f718,plain,(
    k2_enumset1(sK18,sK19,sK20,sK21) != k2_enumset1(sK20,sK21,sK18,sK19) ),
    inference(cnf_transformation,[],[f455])).

fof(f187,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f699,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f187])).

fof(f208,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f719,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f208])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f671,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f777,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f671,f611])).

fof(f778,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f719,f777])).

fof(f780,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f699,f777,f778,f778])).

fof(f953,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19))))))) ),
    inference(definition_unfolding,[],[f718,f780,f780])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f668,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f460,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f789])).

cnf(c_255,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19))))))) ),
    inference(cnf_transformation,[],[f953])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f668])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f460])).

cnf(c_4003,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19))),k5_xboole_0(k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))),k4_xboole_0(k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19))))))))))))) != k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19))),k5_xboole_0(k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19))))),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))))))))) ),
    inference(theory_normalisation,[status(thm)],[c_255,c_211,c_7])).

cnf(c_8443,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_6,c_4003])).

%------------------------------------------------------------------------------
