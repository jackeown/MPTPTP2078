%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0133+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:23 EST 2020

% Result     : Theorem 1.06s
% Output     : CNFRefutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   23 (  70 expanded)
%              Number of clauses        :    2 (   2 expanded)
%              Number of leaves         :    7 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   24 (  71 expanded)
%              Number of equality atoms :   23 (  70 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :   11 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f192,conjecture,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f193,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(negated_conjecture,[],[f192])).

fof(f307,plain,(
    ? [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) != k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(ennf_transformation,[],[f193])).

fof(f382,plain,
    ( ? [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) != k3_enumset1(X0,X1,X2,X3,X4)
   => k2_xboole_0(k1_enumset1(sK18,sK19,sK20),k2_tarski(sK21,sK22)) != k3_enumset1(sK18,sK19,sK20,sK21,sK22) ),
    introduced(choice_axiom,[])).

fof(f383,plain,(
    k2_xboole_0(k1_enumset1(sK18,sK19,sK20),k2_tarski(sK21,sK22)) != k3_enumset1(sK18,sK19,sK20,sK21,sK22) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18,sK19,sK20,sK21,sK22])],[f307,f382])).

fof(f635,plain,(
    k2_xboole_0(k1_enumset1(sK18,sK19,sK20),k2_tarski(sK21,sK22)) != k3_enumset1(sK18,sK19,sK20,sK21,sK22) ),
    inference(cnf_transformation,[],[f383])).

fof(f183,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f626,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f183])).

fof(f185,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f628,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f185])).

fof(f638,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f628,f636,f637])).

fof(f184,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f627,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f184])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f599,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f539,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f636,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f599,f539])).

fof(f637,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f627,f636])).

fof(f640,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))),k5_xboole_0(k5_xboole_0(k1_tarski(X3),k1_tarski(X4)),k4_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X3),k1_tarski(X4))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))),k5_xboole_0(k5_xboole_0(k1_tarski(X3),k1_tarski(X4)),k4_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X3),k1_tarski(X4))))))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f626,f636,f638,f637])).

fof(f798,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22))))))) ),
    inference(definition_unfolding,[],[f635,f636,f638,f637,f640])).

cnf(c_244,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k4_xboole_0(k1_tarski(sK19),k4_xboole_0(k1_tarski(sK19),k1_tarski(sK20))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK21),k1_tarski(sK22)),k4_xboole_0(k1_tarski(sK21),k4_xboole_0(k1_tarski(sK21),k1_tarski(sK22))))))) ),
    inference(cnf_transformation,[],[f798])).

cnf(c_1021,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_244])).

%------------------------------------------------------------------------------
