%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0143+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:23 EST 2020

% Result     : Theorem 1.12s
% Output     : CNFRefutation 1.12s
% Verified   : 
% Statistics : Number of formulae       :   26 ( 102 expanded)
%              Number of clauses        :    2 (   2 expanded)
%              Number of leaves         :    8 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   27 ( 103 expanded)
%              Number of equality atoms :   26 ( 102 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :   11 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f206,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f207,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(negated_conjecture,[],[f206])).

fof(f321,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) != k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(ennf_transformation,[],[f207])).

fof(f396,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) != k5_enumset1(X0,X1,X2,X3,X4,X5,X6)
   => k2_xboole_0(k2_enumset1(sK18,sK19,sK20,sK21),k1_enumset1(sK22,sK23,sK24)) != k5_enumset1(sK18,sK19,sK20,sK21,sK22,sK23,sK24) ),
    introduced(choice_axiom,[])).

fof(f397,plain,(
    k2_xboole_0(k2_enumset1(sK18,sK19,sK20,sK21),k1_enumset1(sK22,sK23,sK24)) != k5_enumset1(sK18,sK19,sK20,sK21,sK22,sK23,sK24) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18,sK19,sK20,sK21,sK22,sK23,sK24])],[f321,f396])).

fof(f661,plain,(
    k2_xboole_0(k2_enumset1(sK18,sK19,sK20,sK21),k1_enumset1(sK22,sK23,sK24)) != k5_enumset1(sK18,sK19,sK20,sK21,sK22,sK23,sK24) ),
    inference(cnf_transformation,[],[f397])).

fof(f187,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f642,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f187])).

fof(f184,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f639,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f184])).

fof(f665,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f639,f662,f663,f663])).

fof(f189,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f644,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f189])).

fof(f188,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f643,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f188])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f613,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f553,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f662,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f613,f553])).

fof(f663,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f643,f662])).

fof(f664,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f644,f662,f663])).

fof(f668,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))))),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k1_tarski(X6)),k4_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X5),k1_tarski(X6))))),k4_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X4),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k1_tarski(X6)),k4_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X5),k1_tarski(X6)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))))),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k1_tarski(X6)),k4_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X5),k1_tarski(X6))))),k4_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X4),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k1_tarski(X6)),k4_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X5),k1_tarski(X6)))))))))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f642,f662,f665,f664])).

fof(f836,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k5_xboole_0(k1_tarski(sK23),k1_tarski(sK24)),k4_xboole_0(k1_tarski(sK23),k4_xboole_0(k1_tarski(sK23),k1_tarski(sK24))))),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k5_xboole_0(k5_xboole_0(k1_tarski(sK23),k1_tarski(sK24)),k4_xboole_0(k1_tarski(sK23),k4_xboole_0(k1_tarski(sK23),k1_tarski(sK24)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k5_xboole_0(k1_tarski(sK23),k1_tarski(sK24)),k4_xboole_0(k1_tarski(sK23),k4_xboole_0(k1_tarski(sK23),k1_tarski(sK24))))),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k5_xboole_0(k5_xboole_0(k1_tarski(sK23),k1_tarski(sK24)),k4_xboole_0(k1_tarski(sK23),k4_xboole_0(k1_tarski(sK23),k1_tarski(sK24)))))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k5_xboole_0(k1_tarski(sK23),k1_tarski(sK24)),k4_xboole_0(k1_tarski(sK23),k4_xboole_0(k1_tarski(sK23),k1_tarski(sK24))))),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k5_xboole_0(k5_xboole_0(k1_tarski(sK23),k1_tarski(sK24)),k4_xboole_0(k1_tarski(sK23),k4_xboole_0(k1_tarski(sK23),k1_tarski(sK24)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k5_xboole_0(k1_tarski(sK23),k1_tarski(sK24)),k4_xboole_0(k1_tarski(sK23),k4_xboole_0(k1_tarski(sK23),k1_tarski(sK24))))),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k5_xboole_0(k5_xboole_0(k1_tarski(sK23),k1_tarski(sK24)),k4_xboole_0(k1_tarski(sK23),k4_xboole_0(k1_tarski(sK23),k1_tarski(sK24)))))))))) ),
    inference(definition_unfolding,[],[f661,f662,f665,f664,f668])).

cnf(c_254,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k5_xboole_0(k1_tarski(sK23),k1_tarski(sK24)),k4_xboole_0(k1_tarski(sK23),k4_xboole_0(k1_tarski(sK23),k1_tarski(sK24))))),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k5_xboole_0(k5_xboole_0(k1_tarski(sK23),k1_tarski(sK24)),k4_xboole_0(k1_tarski(sK23),k4_xboole_0(k1_tarski(sK23),k1_tarski(sK24)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k5_xboole_0(k1_tarski(sK23),k1_tarski(sK24)),k4_xboole_0(k1_tarski(sK23),k4_xboole_0(k1_tarski(sK23),k1_tarski(sK24))))),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k5_xboole_0(k5_xboole_0(k1_tarski(sK23),k1_tarski(sK24)),k4_xboole_0(k1_tarski(sK23),k4_xboole_0(k1_tarski(sK23),k1_tarski(sK24)))))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k5_xboole_0(k1_tarski(sK23),k1_tarski(sK24)),k4_xboole_0(k1_tarski(sK23),k4_xboole_0(k1_tarski(sK23),k1_tarski(sK24))))),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k5_xboole_0(k5_xboole_0(k1_tarski(sK23),k1_tarski(sK24)),k4_xboole_0(k1_tarski(sK23),k4_xboole_0(k1_tarski(sK23),k1_tarski(sK24)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k5_xboole_0(k1_tarski(sK23),k1_tarski(sK24)),k4_xboole_0(k1_tarski(sK23),k4_xboole_0(k1_tarski(sK23),k1_tarski(sK24))))),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k5_xboole_0(k5_xboole_0(k1_tarski(sK23),k1_tarski(sK24)),k4_xboole_0(k1_tarski(sK23),k4_xboole_0(k1_tarski(sK23),k1_tarski(sK24)))))))))) ),
    inference(cnf_transformation,[],[f836])).

cnf(c_1093,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_254])).

%------------------------------------------------------------------------------
