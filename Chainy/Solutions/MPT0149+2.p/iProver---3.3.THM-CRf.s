%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0149+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:23 EST 2020

% Result     : Theorem 1.33s
% Output     : CNFRefutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   23 ( 118 expanded)
%              Number of clauses        :    2 (   2 expanded)
%              Number of leaves         :    7 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   24 ( 119 expanded)
%              Number of equality atoms :   23 ( 118 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :   11 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f214,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f215,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(negated_conjecture,[],[f214])).

fof(f329,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(ennf_transformation,[],[f215])).

fof(f404,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)
   => k2_xboole_0(k2_enumset1(sK18,sK19,sK20,sK21),k2_enumset1(sK22,sK23,sK24,sK25)) != k6_enumset1(sK18,sK19,sK20,sK21,sK22,sK23,sK24,sK25) ),
    introduced(choice_axiom,[])).

fof(f405,plain,(
    k2_xboole_0(k2_enumset1(sK18,sK19,sK20,sK21),k2_enumset1(sK22,sK23,sK24,sK25)) != k6_enumset1(sK18,sK19,sK20,sK21,sK22,sK23,sK24,sK25) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18,sK19,sK20,sK21,sK22,sK23,sK24,sK25])],[f329,f404])).

fof(f676,plain,(
    k2_xboole_0(k2_enumset1(sK18,sK19,sK20,sK21),k2_enumset1(sK22,sK23,sK24,sK25)) != k6_enumset1(sK18,sK19,sK20,sK21,sK22,sK23,sK24,sK25) ),
    inference(cnf_transformation,[],[f405])).

fof(f189,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f651,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f189])).

fof(f185,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f647,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f185])).

fof(f190,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f652,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f190])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f621,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f561,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f677,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f621,f561])).

fof(f678,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f652,f677])).

fof(f680,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f647,f677,f678,f678])).

fof(f684,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X5)),k4_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X4),k1_tarski(X5)))),k5_xboole_0(k5_xboole_0(k1_tarski(X6),k1_tarski(X7)),k4_xboole_0(k1_tarski(X6),k4_xboole_0(k1_tarski(X6),k1_tarski(X7))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X5)),k4_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X4),k1_tarski(X5)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X5)),k4_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X4),k1_tarski(X5)))),k5_xboole_0(k5_xboole_0(k1_tarski(X6),k1_tarski(X7)),k4_xboole_0(k1_tarski(X6),k4_xboole_0(k1_tarski(X6),k1_tarski(X7)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X5)),k4_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X4),k1_tarski(X5)))),k5_xboole_0(k5_xboole_0(k1_tarski(X6),k1_tarski(X7)),k4_xboole_0(k1_tarski(X6),k4_xboole_0(k1_tarski(X6),k1_tarski(X7))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X5)),k4_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X4),k1_tarski(X5)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X5)),k4_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X4),k1_tarski(X5)))),k5_xboole_0(k5_xboole_0(k1_tarski(X6),k1_tarski(X7)),k4_xboole_0(k1_tarski(X6),k4_xboole_0(k1_tarski(X6),k1_tarski(X7)))))))))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f651,f677,f680,f680])).

fof(f858,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k1_tarski(sK25)),k4_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k1_tarski(sK25)),k4_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k1_tarski(sK25)),k4_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k1_tarski(sK25)),k4_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25)))))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k1_tarski(sK25)),k4_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k1_tarski(sK25)),k4_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k1_tarski(sK25)),k4_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k1_tarski(sK25)),k4_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25)))))))))) ),
    inference(definition_unfolding,[],[f676,f677,f680,f680,f684])).

cnf(c_260,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k1_tarski(sK25)),k4_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k1_tarski(sK25)),k4_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k1_tarski(sK25)),k4_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k1_tarski(sK25)),k4_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25)))))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k1_tarski(sK25)),k4_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k1_tarski(sK25)),k4_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK20),k1_tarski(sK21)),k4_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK20),k1_tarski(sK21))))))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k1_tarski(sK25)),k4_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k1_tarski(sK25)),k4_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25)))))))))) ),
    inference(cnf_transformation,[],[f858])).

cnf(c_1105,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_260])).

%------------------------------------------------------------------------------
