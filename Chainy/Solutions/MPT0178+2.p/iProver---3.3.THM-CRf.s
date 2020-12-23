%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0178+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:25 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 325 expanded)
%              Number of clauses        :   20 (  56 expanded)
%              Number of leaves         :   19 ( 108 expanded)
%              Depth                    :   12
%              Number of atoms          :   75 ( 326 expanded)
%              Number of equality atoms :   74 ( 325 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :   28 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f243,conjecture,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f244,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(negated_conjecture,[],[f243])).

fof(f358,plain,(
    ? [X0] : k1_tarski(X0) != k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(ennf_transformation,[],[f244])).

fof(f433,plain,
    ( ? [X0] : k1_tarski(X0) != k5_enumset1(X0,X0,X0,X0,X0,X0,X0)
   => k1_tarski(sK18) != k5_enumset1(sK18,sK18,sK18,sK18,sK18,sK18,sK18) ),
    introduced(choice_axiom,[])).

fof(f434,plain,(
    k1_tarski(sK18) != k5_enumset1(sK18,sK18,sK18,sK18,sK18,sK18,sK18) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f358,f433])).

fof(f734,plain,(
    k1_tarski(sK18) != k5_enumset1(sK18,sK18,sK18,sK18,sK18,sK18,sK18) ),
    inference(cnf_transformation,[],[f434])).

fof(f188,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f679,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f188])).

fof(f185,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f676,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f185])).

fof(f738,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f676,f735,f736,f736])).

fof(f191,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f682,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f191])).

fof(f190,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f681,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f190])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f650,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f590,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f735,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f650,f590])).

fof(f736,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f681,f735])).

fof(f737,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f682,f735,f736])).

fof(f741,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))))),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k1_tarski(X6)),k4_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X5),k1_tarski(X6))))),k4_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X4),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k1_tarski(X6)),k4_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X5),k1_tarski(X6)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))))),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k1_tarski(X6)),k4_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X5),k1_tarski(X6))))),k4_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X4),k5_xboole_0(k5_xboole_0(k1_tarski(X5),k1_tarski(X6)),k4_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X5),k1_tarski(X6)))))))))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f679,f735,f738,f737])).

fof(f945,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))))))))) != k1_tarski(sK18) ),
    inference(definition_unfolding,[],[f734,f741])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f647,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f439,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f580,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f442,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f828,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f580,f442])).

fof(f124,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f604,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f124])).

fof(f847,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f604,f442])).

fof(f164,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f648,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f164])).

fof(f874,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f648,f442])).

fof(f170,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f654,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f170])).

fof(f877,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f654,f735])).

fof(f88,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f567,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

fof(f820,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f567,f590,f442,f442])).

fof(f108,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f588,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f108])).

fof(f836,plain,(
    ! [X0,X1] : o_0_0_xboole_0 = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f588,f442,f735])).

fof(f232,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f723,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f232])).

fof(f186,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f677,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f186])).

fof(f739,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))),k5_xboole_0(k5_xboole_0(k1_tarski(X3),k1_tarski(X4)),k4_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X3),k1_tarski(X4))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))),k5_xboole_0(k5_xboole_0(k1_tarski(X3),k1_tarski(X4)),k4_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X3),k1_tarski(X4))))))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f677,f735,f737,f736])).

fof(f934,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X0)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X0)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0))))))),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X0)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X0)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X0)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X0)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0))))))),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))))) ),
    inference(definition_unfolding,[],[f723,f736,f739])).

cnf(c_289,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))))))))) != k1_tarski(sK18) ),
    inference(cnf_transformation,[],[f945])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f647])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f439])).

cnf(c_3942,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))))),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))))))))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))))))))))),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))))))))))))))))))))))) != k1_tarski(sK18) ),
    inference(theory_normalisation,[status(thm)],[c_289,c_211,c_7])).

cnf(c_145,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f828])).

cnf(c_168,plain,
    ( k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f847])).

cnf(c_212,plain,
    ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f874])).

cnf(c_217,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f877])).

cnf(c_4005,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_217,c_211,c_7])).

cnf(c_132,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f820])).

cnf(c_7757,plain,
    ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_132,c_145])).

cnf(c_153,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f836])).

cnf(c_4026,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = o_0_0_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_153,c_211,c_7])).

cnf(c_7944,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4005,c_4026])).

cnf(c_278,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X0)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X0)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0))))))),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X0)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X0)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X0)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X0)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0))))))),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) ),
    inference(cnf_transformation,[],[f934])).

cnf(c_3953,plain,
    ( k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0))),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1))),k5_xboole_0(k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0))))))),k4_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0))))))))))),k4_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0))))))))))),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))))))))))))) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))) ),
    inference(theory_normalisation,[status(thm)],[c_278,c_211,c_7])).

cnf(c_8695,plain,
    ( k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) ),
    inference(demodulation,[status(thm)],[c_3953,c_145,c_168,c_212,c_4005,c_7757,c_7944])).

cnf(c_8733,plain,
    ( k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k1_tarski(sK18))))))))))))))) != k1_tarski(sK18) ),
    inference(demodulation,[status(thm)],[c_3942,c_145,c_168,c_212,c_4005,c_7757,c_7944,c_8695])).

cnf(c_8734,plain,
    ( k1_tarski(sK18) != k1_tarski(sK18) ),
    inference(demodulation,[status(thm)],[c_8733,c_145,c_168,c_212,c_7757])).

cnf(c_8735,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_8734])).

%------------------------------------------------------------------------------
