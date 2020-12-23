%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0158+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:24 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 263 expanded)
%              Number of clauses        :   25 (  48 expanded)
%              Number of leaves         :   19 (  86 expanded)
%              Depth                    :   15
%              Number of atoms          :   80 ( 264 expanded)
%              Number of equality atoms :   79 ( 263 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :   28 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f418,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f570,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f707,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f418,f570,f570])).

fof(f164,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f628,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f164])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f422,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f834,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f628,f422])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f627,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f124,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f584,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f124])).

fof(f807,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f584,f422])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f419,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f223,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f224,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(negated_conjecture,[],[f223])).

fof(f338,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(ennf_transformation,[],[f224])).

fof(f413,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k5_enumset1(X0,X0,X1,X2,X3,X4,X5)
   => k4_enumset1(sK18,sK19,sK20,sK21,sK22,sK23) != k5_enumset1(sK18,sK18,sK19,sK20,sK21,sK22,sK23) ),
    introduced(choice_axiom,[])).

fof(f414,plain,(
    k4_enumset1(sK18,sK19,sK20,sK21,sK22,sK23) != k5_enumset1(sK18,sK18,sK19,sK20,sK21,sK22,sK23) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18,sK19,sK20,sK21,sK22,sK23])],[f338,f413])).

fof(f694,plain,(
    k4_enumset1(sK18,sK19,sK20,sK21,sK22,sK23) != k5_enumset1(sK18,sK18,sK19,sK20,sK21,sK22,sK23) ),
    inference(cnf_transformation,[],[f414])).

fof(f187,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f658,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f187])).

fof(f700,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))),k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X5)),k4_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X4),k1_tarski(X5))))),k4_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X3),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X5)),k4_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X4),k1_tarski(X5)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))),k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X5)),k4_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X4),k1_tarski(X5))))),k4_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X3),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X5)),k4_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X4),k1_tarski(X5)))))))))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f658,f695,f697,f697])).

fof(f188,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f659,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f188])).

fof(f185,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f656,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f185])).

fof(f698,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f656,f695,f696,f696])).

fof(f191,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f662,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f191])).

fof(f190,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f661,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f190])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f630,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f695,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f630,f570])).

fof(f696,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f661,f695])).

fof(f697,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f662,f695,f696])).

fof(f701,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))))),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k1_tarski(X6)),k4_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X5),k1_tarski(X6))))),k4_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X4),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k1_tarski(X6)),k4_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X5),k1_tarski(X6)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))))),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k1_tarski(X6)),k4_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X5),k1_tarski(X6))))),k4_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X4),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k1_tarski(X6)),k4_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X5),k1_tarski(X6)))))))))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f659,f695,f698,f697])).

fof(f885,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))))))))) ),
    inference(definition_unfolding,[],[f694,f700,f701])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f560,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f788,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f560,f422])).

fof(f170,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f634,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f170])).

fof(f837,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f634,f695])).

fof(f88,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f547,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

fof(f780,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f547,f570,f422,f422])).

fof(f103,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f563,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f103])).

fof(f791,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f563,f695])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f707])).

cnf(c_212,plain,
    ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f834])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f627])).

cnf(c_10053,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(o_0_0_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_212,c_211])).

cnf(c_168,plain,
    ( k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f807])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f419])).

cnf(c_9224,plain,
    ( k5_xboole_0(o_0_0_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_168,c_7])).

cnf(c_10093,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_10053,c_9224])).

cnf(c_269,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k5_xboole_0(k5_xboole_0(k1_tarski(sK22),k1_tarski(sK23)),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23)))))))))) ),
    inference(cnf_transformation,[],[f885])).

cnf(c_3862,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k5_xboole_0(k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))))))),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))))))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))))))))),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))))))))))))))))))))))))) != k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k5_xboole_0(k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))))))),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))))))))))))))))))))))) ),
    inference(theory_normalisation,[status(thm)],[c_269,c_211,c_7])).

cnf(c_145,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f788])).

cnf(c_217,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f837])).

cnf(c_3905,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_217,c_211,c_7])).

cnf(c_132,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f780])).

cnf(c_7597,plain,
    ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_132,c_145])).

cnf(c_148,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f791])).

cnf(c_3931,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(theory_normalisation,[status(thm)],[c_148,c_211,c_7])).

cnf(c_7846,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_3931,c_3905])).

cnf(c_8565,plain,
    ( k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k5_xboole_0(k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))),k1_tarski(sK19)),k1_tarski(sK20))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))),k1_tarski(sK19)),k1_tarski(sK20))))))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))),k1_tarski(sK19)),k1_tarski(sK20))))))))),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))))))))))))))))))))) != k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))),k5_xboole_0(k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))))))),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))))))))))))))))))) ),
    inference(demodulation,[status(thm)],[c_3862,c_145,c_3905,c_7597,c_7846])).

cnf(c_8566,plain,
    ( k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k5_xboole_0(k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))))))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))))))))),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))))))))))))))))))))) != k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))),k5_xboole_0(k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))))))),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))))))))))))))))))) ),
    inference(demodulation,[status(thm)],[c_8565,c_168,c_7597])).

cnf(c_9303,plain,
    ( k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k5_xboole_0(k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))),k4_xboole_0(k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))))))),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))))))))))))))))))))))) != k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))),k5_xboole_0(k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))))))),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))))))))))))))))))) ),
    inference(demodulation,[status(thm)],[c_6,c_8566])).

cnf(c_10788,plain,
    ( k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k5_xboole_0(k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))),k4_xboole_0(k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))))))),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))))))))))))))))))))) != k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))),k5_xboole_0(k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))))))),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))))))))))))))))))) ),
    inference(demodulation,[status(thm)],[c_10093,c_9303])).

cnf(c_10790,plain,
    ( k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k5_xboole_0(k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))),k4_xboole_0(k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))))))),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))))))))))))))))))) != k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))),k5_xboole_0(k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))))))),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))))))))))))))))))) ),
    inference(demodulation,[status(thm)],[c_10788,c_10093])).

cnf(c_10889,plain,
    ( k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k5_xboole_0(k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))),k4_xboole_0(k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))))))),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))))))))))))))))))) != k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))),k5_xboole_0(k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK19),k5_xboole_0(k1_tarski(sK20),k5_xboole_0(k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k4_xboole_0(k1_tarski(sK18),k1_tarski(sK19)),k1_tarski(sK20))))))),k5_xboole_0(k1_tarski(sK21),k5_xboole_0(k1_tarski(sK22),k5_xboole_0(k1_tarski(sK23),k5_xboole_0(k4_xboole_0(k1_tarski(sK22),k4_xboole_0(k1_tarski(sK22),k1_tarski(sK23))),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k1_tarski(sK23))))))))))))))))))) ),
    inference(superposition,[status(thm)],[c_6,c_10790])).

cnf(c_10891,plain,
    ( $false ),
    inference(theory_normalisation,[status(thm)],[c_10889])).

%------------------------------------------------------------------------------
