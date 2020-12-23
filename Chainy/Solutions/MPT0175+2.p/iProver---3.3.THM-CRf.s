%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0175+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:25 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 143 expanded)
%              Number of clauses        :   16 (  25 expanded)
%              Number of leaves         :   16 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   62 ( 144 expanded)
%              Number of equality atoms :   61 ( 143 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :   24 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f240,conjecture,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f241,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(negated_conjecture,[],[f240])).

fof(f355,plain,(
    ? [X0] : k1_tarski(X0) != k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(ennf_transformation,[],[f241])).

fof(f430,plain,
    ( ? [X0] : k1_tarski(X0) != k4_enumset1(X0,X0,X0,X0,X0,X0)
   => k1_tarski(sK18) != k4_enumset1(sK18,sK18,sK18,sK18,sK18,sK18) ),
    introduced(choice_axiom,[])).

fof(f431,plain,(
    k1_tarski(sK18) != k4_enumset1(sK18,sK18,sK18,sK18,sK18,sK18) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f355,f430])).

fof(f728,plain,(
    k1_tarski(sK18) != k4_enumset1(sK18,sK18,sK18,sK18,sK18,sK18) ),
    inference(cnf_transformation,[],[f431])).

fof(f187,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f675,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f187])).

fof(f191,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f679,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f191])).

fof(f190,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f678,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f190])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f647,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f587,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f729,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f647,f587])).

fof(f730,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f678,f729])).

fof(f731,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f679,f729,f730])).

fof(f734,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))),k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X5)),k4_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X4),k1_tarski(X5))))),k4_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X3),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X5)),k4_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X4),k1_tarski(X5)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))),k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X5)),k4_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X4),k1_tarski(X5))))),k4_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X3),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X5)),k4_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X4),k1_tarski(X5)))))))))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f675,f729,f731,f731])).

fof(f936,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))))))))) != k1_tarski(sK18) ),
    inference(definition_unfolding,[],[f728,f734])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f644,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f436,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f577,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f439,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f822,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f577,f439])).

fof(f124,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f601,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f124])).

fof(f841,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f601,f439])).

fof(f164,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f645,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f164])).

fof(f868,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f645,f439])).

fof(f170,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f651,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f170])).

fof(f871,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f651,f729])).

fof(f88,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f564,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

fof(f814,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f564,f587,f439,f439])).

fof(f108,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f585,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f108])).

fof(f830,plain,(
    ! [X0,X1] : o_0_0_xboole_0 = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f585,f439,f729])).

cnf(c_286,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k5_xboole_0(k1_tarski(sK18),k1_tarski(sK18)),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18)))))))))) != k1_tarski(sK18) ),
    inference(cnf_transformation,[],[f936])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f644])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f436])).

cnf(c_3930,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))))),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))))))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))))))))),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k5_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k4_xboole_0(k1_tarski(sK18),k1_tarski(sK18))))))))))))))))))))))) != k1_tarski(sK18) ),
    inference(theory_normalisation,[status(thm)],[c_286,c_211,c_7])).

cnf(c_145,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f822])).

cnf(c_168,plain,
    ( k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f841])).

cnf(c_212,plain,
    ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f868])).

cnf(c_217,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f871])).

cnf(c_3990,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_217,c_211,c_7])).

cnf(c_132,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f814])).

cnf(c_7733,plain,
    ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_132,c_145])).

cnf(c_153,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f830])).

cnf(c_4011,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = o_0_0_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_153,c_211,c_7])).

cnf(c_7920,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3990,c_4011])).

cnf(c_8692,plain,
    ( k1_tarski(sK18) != k1_tarski(sK18) ),
    inference(demodulation,[status(thm)],[c_3930,c_145,c_168,c_212,c_3990,c_7733,c_7920])).

cnf(c_8693,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_8692])).

%------------------------------------------------------------------------------
