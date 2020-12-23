%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0137+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:23 EST 2020

% Result     : Theorem 1.02s
% Output     : CNFRefutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :   23 (  86 expanded)
%              Number of clauses        :    2 (   2 expanded)
%              Number of leaves         :    7 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   24 (  87 expanded)
%              Number of equality atoms :   23 (  86 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :   11 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f198,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f199,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(negated_conjecture,[],[f198])).

fof(f313,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) != k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(ennf_transformation,[],[f199])).

fof(f388,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) != k4_enumset1(X0,X1,X2,X3,X4,X5)
   => k2_xboole_0(k1_enumset1(sK18,sK19,sK20),k1_enumset1(sK21,sK22,sK23)) != k4_enumset1(sK18,sK19,sK20,sK21,sK22,sK23) ),
    introduced(choice_axiom,[])).

fof(f389,plain,(
    k2_xboole_0(k1_enumset1(sK18,sK19,sK20),k1_enumset1(sK21,sK22,sK23)) != k4_enumset1(sK18,sK19,sK20,sK21,sK22,sK23) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18,sK19,sK20,sK21,sK22,sK23])],[f313,f388])).

fof(f646,plain,(
    k2_xboole_0(k1_enumset1(sK18,sK19,sK20),k1_enumset1(sK21,sK22,sK23)) != k4_enumset1(sK18,sK19,sK20,sK21,sK22,sK23) ),
    inference(cnf_transformation,[],[f389])).

fof(f185,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f633,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f185])).

fof(f187,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f635,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f187])).

fof(f186,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f634,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f186])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f605,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f545,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f647,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f605,f545])).

fof(f648,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f634,f647])).

fof(f649,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f635,f647,f648])).

fof(f652,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))),k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X5)),k4_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X4),k1_tarski(X5))))),k4_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X3),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X5)),k4_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X4),k1_tarski(X5)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))),k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X5)),k4_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X4),k1_tarski(X5))))),k4_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X3),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X5)),k4_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X4),k1_tarski(X5)))))))))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f633,f647,f649,f649])).

fof(f814,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))))))))) ),
    inference(definition_unfolding,[],[f646,f647,f649,f649,f652])).

cnf(c_248,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))))))))) ),
    inference(cnf_transformation,[],[f814])).

cnf(c_1029,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_248])).

%------------------------------------------------------------------------------
