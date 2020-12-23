%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:28:18 EST 2020

% Result     : Theorem 12.21s
% Output     : CNFRefutation 12.21s
% Verified   : 
% Statistics : Number of formulae       :   79 (  96 expanded)
%              Number of clauses        :   51 (  64 expanded)
%              Number of leaves         :   14 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :  134 ( 167 expanded)
%              Number of equality atoms :  133 ( 166 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f21,f25])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f20,f25])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) != k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(ennf_transformation,[],[f12])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) != k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
   => k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f13,f14])).

fof(f26,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(definition_unfolding,[],[f18,f22])).

fof(f31,plain,(
    k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(definition_unfolding,[],[f26,f24,f27])).

cnf(c_26,plain,
    ( X0_40 != X1_40
    | X2_40 != X1_40
    | X2_40 = X0_40 ),
    theory(equality)).

cnf(c_75,plain,
    ( k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) != X0_40
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != X0_40
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_134,plain,
    ( k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) != k2_xboole_0(X0_40,X1_40)
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(X0_40,X1_40)
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_75])).

cnf(c_46554,plain,
    ( k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) != k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3))
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_3,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_21,plain,
    ( k2_xboole_0(k2_xboole_0(X0_40,X1_40),X2_40) = k2_xboole_0(X0_40,k2_xboole_0(X1_40,X2_40)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_28490,plain,
    ( k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_121,plain,
    ( k2_xboole_0(X0_40,X1_40) != X2_40
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != X2_40
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(X0_40,X1_40) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_10100,plain,
    ( k2_xboole_0(X0_40,X1_40) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)))
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(X0_40,X1_40)
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_121])).

cnf(c_28489,plain,
    ( k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)))
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_10100])).

cnf(c_133,plain,
    ( X0_40 != X1_40
    | k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) != X1_40
    | k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) = X0_40 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_280,plain,
    ( X0_40 != k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) = X0_40
    | k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_16586,plain,
    ( k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) = k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_280])).

cnf(c_27,plain,
    ( X0_40 != X1_40
    | X2_40 != X3_40
    | k2_xboole_0(X0_40,X2_40) = k2_xboole_0(X1_40,X3_40) ),
    theory(equality)).

cnf(c_197,plain,
    ( X0_40 != k3_enumset1(sK4,sK5,sK6,sK7,sK8)
    | X1_40 != k3_enumset1(sK0,sK0,sK1,sK2,sK3)
    | k2_xboole_0(X1_40,X0_40) = k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_476,plain,
    ( X0_40 != k3_enumset1(sK0,sK0,sK1,sK2,sK3)
    | k3_enumset1(sK4,sK5,sK6,sK7,sK8) != k3_enumset1(sK4,sK5,sK6,sK7,sK8)
    | k2_xboole_0(X0_40,k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_197])).

cnf(c_5584,plain,
    ( k3_enumset1(sK4,sK5,sK6,sK7,sK8) != k3_enumset1(sK4,sK5,sK6,sK7,sK8)
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)
    | k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_476])).

cnf(c_213,plain,
    ( k2_xboole_0(X0_40,X1_40) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(X0_40,X1_40)
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_121])).

cnf(c_3533,plain,
    ( k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)))
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_213])).

cnf(c_412,plain,
    ( X0_40 != k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)
    | X1_40 != k3_enumset1(sK0,sK0,sK0,sK1,sK2)
    | k2_xboole_0(X1_40,X0_40) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_845,plain,
    ( X0_40 != k3_enumset1(sK0,sK0,sK0,sK1,sK2)
    | k2_xboole_0(X0_40,k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_412])).

cnf(c_2145,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2)
    | k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_845])).

cnf(c_372,plain,
    ( X0_40 != X1_40
    | X0_40 = k3_enumset1(sK0,sK0,sK1,sK2,sK3)
    | k3_enumset1(sK0,sK0,sK1,sK2,sK3) != X1_40 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_826,plain,
    ( X0_40 != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)
    | X0_40 = k3_enumset1(sK0,sK0,sK1,sK2,sK3)
    | k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_1865,plain,
    ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) = k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_826])).

cnf(c_4,plain,
    ( k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_20,plain,
    ( k2_xboole_0(k3_enumset1(X0_41,X1_41,X2_41,X3_41,X4_41),k4_enumset1(X5_41,X5_41,X5_41,X5_41,X5_41,X5_41)) = k4_enumset1(X0_41,X1_41,X2_41,X3_41,X4_41,X5_41) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_954,plain,
    ( k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) = k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_0,plain,
    ( k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_24,plain,
    ( k2_xboole_0(k4_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k3_enumset1(X1_41,X2_41,X3_41,X4_41,X5_41)) = k4_enumset1(X0_41,X1_41,X2_41,X3_41,X4_41,X5_41) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_846,plain,
    ( k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_5,plain,
    ( k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_19,plain,
    ( k4_enumset1(X0_41,X0_41,X1_41,X2_41,X3_41,X4_41) = k3_enumset1(X0_41,X1_41,X2_41,X3_41,X4_41) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_368,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) = k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_128,plain,
    ( X0_40 != X1_40
    | k3_enumset1(sK0,sK0,sK1,sK2,sK3) != X1_40
    | k3_enumset1(sK0,sK0,sK1,sK2,sK3) = X0_40 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_209,plain,
    ( X0_40 != k3_enumset1(sK0,sK0,sK1,sK2,sK3)
    | k3_enumset1(sK0,sK0,sK1,sK2,sK3) = X0_40
    | k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_128])).

cnf(c_367,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)
    | k3_enumset1(sK0,sK0,sK1,sK2,sK3) = k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)
    | k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_209])).

cnf(c_25,plain,
    ( X0_40 = X0_40 ),
    theory(equality)).

cnf(c_288,plain,
    ( k3_enumset1(sK4,sK5,sK6,sK7,sK8) = k3_enumset1(sK4,sK5,sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_214,plain,
    ( k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_144,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK1,sK2) = k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_22,plain,
    ( k2_xboole_0(X0_40,X1_40) = k2_xboole_0(X1_40,X0_40) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_131,plain,
    ( k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_126,plain,
    ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) = k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_67,plain,
    ( k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_46,plain,
    ( k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != X0_40
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != X0_40 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_66,plain,
    ( k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3))
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_6,negated_conjecture,
    ( k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_18,negated_conjecture,
    ( k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_46554,c_28490,c_28489,c_16586,c_5584,c_3533,c_2145,c_1865,c_954,c_846,c_368,c_367,c_288,c_214,c_144,c_131,c_126,c_67,c_66,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:33:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 12.21/2.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.21/2.05  
% 12.21/2.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 12.21/2.05  
% 12.21/2.05  ------  iProver source info
% 12.21/2.05  
% 12.21/2.05  git: date: 2020-06-30 10:37:57 +0100
% 12.21/2.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 12.21/2.05  git: non_committed_changes: false
% 12.21/2.05  git: last_make_outside_of_git: false
% 12.21/2.05  
% 12.21/2.05  ------ 
% 12.21/2.05  ------ Parsing...
% 12.21/2.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 12.21/2.05  
% 12.21/2.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 12.21/2.05  
% 12.21/2.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 12.21/2.05  
% 12.21/2.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 12.21/2.05  ------ Proving...
% 12.21/2.05  ------ Problem Properties 
% 12.21/2.05  
% 12.21/2.05  
% 12.21/2.05  clauses                                 7
% 12.21/2.05  conjectures                             1
% 12.21/2.05  EPR                                     0
% 12.21/2.05  Horn                                    7
% 12.21/2.05  unary                                   7
% 12.21/2.05  binary                                  0
% 12.21/2.05  lits                                    7
% 12.21/2.05  lits eq                                 7
% 12.21/2.05  fd_pure                                 0
% 12.21/2.05  fd_pseudo                               0
% 12.21/2.05  fd_cond                                 0
% 12.21/2.05  fd_pseudo_cond                          0
% 12.21/2.05  AC symbols                              1
% 12.21/2.05  
% 12.21/2.05  ------ Input Options Time Limit: Unbounded
% 12.21/2.05  
% 12.21/2.05  
% 12.21/2.05  ------ 
% 12.21/2.05  Current options:
% 12.21/2.05  ------ 
% 12.21/2.05  
% 12.21/2.05  
% 12.21/2.05  
% 12.21/2.05  
% 12.21/2.05  ------ Proving...
% 12.21/2.05  
% 12.21/2.05  
% 12.21/2.05  % SZS status Theorem for theBenchmark.p
% 12.21/2.05  
% 12.21/2.05  % SZS output start CNFRefutation for theBenchmark.p
% 12.21/2.05  
% 12.21/2.05  fof(f2,axiom,(
% 12.21/2.05    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 12.21/2.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.21/2.05  
% 12.21/2.05  fof(f17,plain,(
% 12.21/2.05    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 12.21/2.05    inference(cnf_transformation,[],[f2])).
% 12.21/2.05  
% 12.21/2.05  fof(f6,axiom,(
% 12.21/2.05    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 12.21/2.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.21/2.05  
% 12.21/2.05  fof(f21,plain,(
% 12.21/2.05    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 12.21/2.05    inference(cnf_transformation,[],[f6])).
% 12.21/2.05  
% 12.21/2.05  fof(f10,axiom,(
% 12.21/2.05    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)),
% 12.21/2.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.21/2.05  
% 12.21/2.05  fof(f25,plain,(
% 12.21/2.05    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 12.21/2.05    inference(cnf_transformation,[],[f10])).
% 12.21/2.05  
% 12.21/2.05  fof(f30,plain,(
% 12.21/2.05    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 12.21/2.05    inference(definition_unfolding,[],[f21,f25])).
% 12.21/2.05  
% 12.21/2.05  fof(f5,axiom,(
% 12.21/2.05    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 12.21/2.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.21/2.05  
% 12.21/2.05  fof(f20,plain,(
% 12.21/2.05    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 12.21/2.05    inference(cnf_transformation,[],[f5])).
% 12.21/2.05  
% 12.21/2.05  fof(f28,plain,(
% 12.21/2.05    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 12.21/2.05    inference(definition_unfolding,[],[f20,f25])).
% 12.21/2.05  
% 12.21/2.05  fof(f8,axiom,(
% 12.21/2.05    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 12.21/2.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.21/2.05  
% 12.21/2.05  fof(f23,plain,(
% 12.21/2.05    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 12.21/2.05    inference(cnf_transformation,[],[f8])).
% 12.21/2.05  
% 12.21/2.05  fof(f1,axiom,(
% 12.21/2.05    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 12.21/2.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.21/2.05  
% 12.21/2.05  fof(f16,plain,(
% 12.21/2.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 12.21/2.05    inference(cnf_transformation,[],[f1])).
% 12.21/2.05  
% 12.21/2.05  fof(f11,conjecture,(
% 12.21/2.05    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 12.21/2.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.21/2.05  
% 12.21/2.05  fof(f12,negated_conjecture,(
% 12.21/2.05    ~! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 12.21/2.05    inference(negated_conjecture,[],[f11])).
% 12.21/2.05  
% 12.21/2.05  fof(f13,plain,(
% 12.21/2.05    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) != k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 12.21/2.05    inference(ennf_transformation,[],[f12])).
% 12.21/2.05  
% 12.21/2.05  fof(f14,plain,(
% 12.21/2.05    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) != k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) => k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),
% 12.21/2.05    introduced(choice_axiom,[])).
% 12.21/2.05  
% 12.21/2.05  fof(f15,plain,(
% 12.21/2.05    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),
% 12.21/2.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f13,f14])).
% 12.21/2.05  
% 12.21/2.05  fof(f26,plain,(
% 12.21/2.05    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),
% 12.21/2.05    inference(cnf_transformation,[],[f15])).
% 12.21/2.05  
% 12.21/2.05  fof(f9,axiom,(
% 12.21/2.05    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 12.21/2.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.21/2.05  
% 12.21/2.05  fof(f24,plain,(
% 12.21/2.05    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 12.21/2.05    inference(cnf_transformation,[],[f9])).
% 12.21/2.05  
% 12.21/2.05  fof(f3,axiom,(
% 12.21/2.05    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 12.21/2.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.21/2.05  
% 12.21/2.05  fof(f18,plain,(
% 12.21/2.05    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 12.21/2.05    inference(cnf_transformation,[],[f3])).
% 12.21/2.05  
% 12.21/2.05  fof(f7,axiom,(
% 12.21/2.05    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 12.21/2.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.21/2.05  
% 12.21/2.05  fof(f22,plain,(
% 12.21/2.05    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 12.21/2.05    inference(cnf_transformation,[],[f7])).
% 12.21/2.05  
% 12.21/2.05  fof(f27,plain,(
% 12.21/2.05    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 12.21/2.05    inference(definition_unfolding,[],[f18,f22])).
% 12.21/2.05  
% 12.21/2.05  fof(f31,plain,(
% 12.21/2.05    k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))),
% 12.21/2.05    inference(definition_unfolding,[],[f26,f24,f27])).
% 12.21/2.05  
% 12.21/2.05  cnf(c_26,plain,
% 12.21/2.05      ( X0_40 != X1_40 | X2_40 != X1_40 | X2_40 = X0_40 ),
% 12.21/2.05      theory(equality) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_75,plain,
% 12.21/2.05      ( k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) != X0_40
% 12.21/2.05      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != X0_40
% 12.21/2.05      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) ),
% 12.21/2.05      inference(instantiation,[status(thm)],[c_26]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_134,plain,
% 12.21/2.05      ( k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) != k2_xboole_0(X0_40,X1_40)
% 12.21/2.05      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(X0_40,X1_40)
% 12.21/2.05      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) ),
% 12.21/2.05      inference(instantiation,[status(thm)],[c_75]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_46554,plain,
% 12.21/2.05      ( k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) != k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8))
% 12.21/2.05      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3))
% 12.21/2.05      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
% 12.21/2.05      inference(instantiation,[status(thm)],[c_134]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_3,plain,
% 12.21/2.05      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 12.21/2.05      inference(cnf_transformation,[],[f17]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_21,plain,
% 12.21/2.05      ( k2_xboole_0(k2_xboole_0(X0_40,X1_40),X2_40) = k2_xboole_0(X0_40,k2_xboole_0(X1_40,X2_40)) ),
% 12.21/2.05      inference(subtyping,[status(esa)],[c_3]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_28490,plain,
% 12.21/2.05      ( k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) ),
% 12.21/2.05      inference(instantiation,[status(thm)],[c_21]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_121,plain,
% 12.21/2.05      ( k2_xboole_0(X0_40,X1_40) != X2_40
% 12.21/2.05      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != X2_40
% 12.21/2.05      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(X0_40,X1_40) ),
% 12.21/2.05      inference(instantiation,[status(thm)],[c_26]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_10100,plain,
% 12.21/2.05      ( k2_xboole_0(X0_40,X1_40) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)))
% 12.21/2.05      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(X0_40,X1_40)
% 12.21/2.05      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) ),
% 12.21/2.05      inference(instantiation,[status(thm)],[c_121]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_28489,plain,
% 12.21/2.05      ( k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)))
% 12.21/2.05      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8))
% 12.21/2.05      | k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) ),
% 12.21/2.05      inference(instantiation,[status(thm)],[c_10100]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_133,plain,
% 12.21/2.05      ( X0_40 != X1_40
% 12.21/2.05      | k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) != X1_40
% 12.21/2.05      | k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) = X0_40 ),
% 12.21/2.05      inference(instantiation,[status(thm)],[c_26]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_280,plain,
% 12.21/2.05      ( X0_40 != k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))
% 12.21/2.05      | k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) = X0_40
% 12.21/2.05      | k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
% 12.21/2.05      inference(instantiation,[status(thm)],[c_133]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_16586,plain,
% 12.21/2.05      ( k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))
% 12.21/2.05      | k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) = k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8))
% 12.21/2.05      | k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
% 12.21/2.05      inference(instantiation,[status(thm)],[c_280]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_27,plain,
% 12.21/2.05      ( X0_40 != X1_40
% 12.21/2.05      | X2_40 != X3_40
% 12.21/2.05      | k2_xboole_0(X0_40,X2_40) = k2_xboole_0(X1_40,X3_40) ),
% 12.21/2.05      theory(equality) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_197,plain,
% 12.21/2.05      ( X0_40 != k3_enumset1(sK4,sK5,sK6,sK7,sK8)
% 12.21/2.05      | X1_40 != k3_enumset1(sK0,sK0,sK1,sK2,sK3)
% 12.21/2.05      | k2_xboole_0(X1_40,X0_40) = k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
% 12.21/2.05      inference(instantiation,[status(thm)],[c_27]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_476,plain,
% 12.21/2.05      ( X0_40 != k3_enumset1(sK0,sK0,sK1,sK2,sK3)
% 12.21/2.05      | k3_enumset1(sK4,sK5,sK6,sK7,sK8) != k3_enumset1(sK4,sK5,sK6,sK7,sK8)
% 12.21/2.05      | k2_xboole_0(X0_40,k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
% 12.21/2.05      inference(instantiation,[status(thm)],[c_197]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_5584,plain,
% 12.21/2.05      ( k3_enumset1(sK4,sK5,sK6,sK7,sK8) != k3_enumset1(sK4,sK5,sK6,sK7,sK8)
% 12.21/2.05      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)
% 12.21/2.05      | k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
% 12.21/2.05      inference(instantiation,[status(thm)],[c_476]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_213,plain,
% 12.21/2.05      ( k2_xboole_0(X0_40,X1_40) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))
% 12.21/2.05      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(X0_40,X1_40)
% 12.21/2.05      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
% 12.21/2.05      inference(instantiation,[status(thm)],[c_121]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_3533,plain,
% 12.21/2.05      ( k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))
% 12.21/2.05      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)))
% 12.21/2.05      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
% 12.21/2.05      inference(instantiation,[status(thm)],[c_213]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_412,plain,
% 12.21/2.05      ( X0_40 != k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)
% 12.21/2.05      | X1_40 != k3_enumset1(sK0,sK0,sK0,sK1,sK2)
% 12.21/2.05      | k2_xboole_0(X1_40,X0_40) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
% 12.21/2.05      inference(instantiation,[status(thm)],[c_27]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_845,plain,
% 12.21/2.05      ( X0_40 != k3_enumset1(sK0,sK0,sK0,sK1,sK2)
% 12.21/2.05      | k2_xboole_0(X0_40,k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))
% 12.21/2.05      | k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) ),
% 12.21/2.05      inference(instantiation,[status(thm)],[c_412]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_2145,plain,
% 12.21/2.05      ( k3_enumset1(sK0,sK0,sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2)
% 12.21/2.05      | k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)
% 12.21/2.05      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
% 12.21/2.05      inference(instantiation,[status(thm)],[c_845]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_372,plain,
% 12.21/2.05      ( X0_40 != X1_40
% 12.21/2.05      | X0_40 = k3_enumset1(sK0,sK0,sK1,sK2,sK3)
% 12.21/2.05      | k3_enumset1(sK0,sK0,sK1,sK2,sK3) != X1_40 ),
% 12.21/2.05      inference(instantiation,[status(thm)],[c_26]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_826,plain,
% 12.21/2.05      ( X0_40 != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)
% 12.21/2.05      | X0_40 = k3_enumset1(sK0,sK0,sK1,sK2,sK3)
% 12.21/2.05      | k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
% 12.21/2.05      inference(instantiation,[status(thm)],[c_372]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_1865,plain,
% 12.21/2.05      ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)
% 12.21/2.05      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)
% 12.21/2.05      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) = k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
% 12.21/2.05      inference(instantiation,[status(thm)],[c_826]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_4,plain,
% 12.21/2.05      ( k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 12.21/2.05      inference(cnf_transformation,[],[f30]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_20,plain,
% 12.21/2.05      ( k2_xboole_0(k3_enumset1(X0_41,X1_41,X2_41,X3_41,X4_41),k4_enumset1(X5_41,X5_41,X5_41,X5_41,X5_41,X5_41)) = k4_enumset1(X0_41,X1_41,X2_41,X3_41,X4_41,X5_41) ),
% 12.21/2.05      inference(subtyping,[status(esa)],[c_4]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_954,plain,
% 12.21/2.05      ( k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) = k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
% 12.21/2.05      inference(instantiation,[status(thm)],[c_20]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_0,plain,
% 12.21/2.05      ( k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 12.21/2.05      inference(cnf_transformation,[],[f28]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_24,plain,
% 12.21/2.05      ( k2_xboole_0(k4_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k3_enumset1(X1_41,X2_41,X3_41,X4_41,X5_41)) = k4_enumset1(X0_41,X1_41,X2_41,X3_41,X4_41,X5_41) ),
% 12.21/2.05      inference(subtyping,[status(esa)],[c_0]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_846,plain,
% 12.21/2.05      ( k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) ),
% 12.21/2.05      inference(instantiation,[status(thm)],[c_24]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_5,plain,
% 12.21/2.05      ( k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
% 12.21/2.05      inference(cnf_transformation,[],[f23]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_19,plain,
% 12.21/2.05      ( k4_enumset1(X0_41,X0_41,X1_41,X2_41,X3_41,X4_41) = k3_enumset1(X0_41,X1_41,X2_41,X3_41,X4_41) ),
% 12.21/2.05      inference(subtyping,[status(esa)],[c_5]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_368,plain,
% 12.21/2.05      ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) = k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
% 12.21/2.05      inference(instantiation,[status(thm)],[c_19]) ).
% 12.21/2.05  
% 12.21/2.05  cnf(c_128,plain,
% 12.21/2.05      ( X0_40 != X1_40
% 12.21/2.05      | k3_enumset1(sK0,sK0,sK1,sK2,sK3) != X1_40
% 12.21/2.05      | k3_enumset1(sK0,sK0,sK1,sK2,sK3) = X0_40 ),
% 12.21/2.06      inference(instantiation,[status(thm)],[c_26]) ).
% 12.21/2.06  
% 12.21/2.06  cnf(c_209,plain,
% 12.21/2.06      ( X0_40 != k3_enumset1(sK0,sK0,sK1,sK2,sK3)
% 12.21/2.06      | k3_enumset1(sK0,sK0,sK1,sK2,sK3) = X0_40
% 12.21/2.06      | k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
% 12.21/2.06      inference(instantiation,[status(thm)],[c_128]) ).
% 12.21/2.06  
% 12.21/2.06  cnf(c_367,plain,
% 12.21/2.06      ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)
% 12.21/2.06      | k3_enumset1(sK0,sK0,sK1,sK2,sK3) = k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)
% 12.21/2.06      | k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
% 12.21/2.06      inference(instantiation,[status(thm)],[c_209]) ).
% 12.21/2.06  
% 12.21/2.06  cnf(c_25,plain,( X0_40 = X0_40 ),theory(equality) ).
% 12.21/2.06  
% 12.21/2.06  cnf(c_288,plain,
% 12.21/2.06      ( k3_enumset1(sK4,sK5,sK6,sK7,sK8) = k3_enumset1(sK4,sK5,sK6,sK7,sK8) ),
% 12.21/2.06      inference(instantiation,[status(thm)],[c_25]) ).
% 12.21/2.06  
% 12.21/2.06  cnf(c_214,plain,
% 12.21/2.06      ( k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
% 12.21/2.06      inference(instantiation,[status(thm)],[c_25]) ).
% 12.21/2.06  
% 12.21/2.06  cnf(c_144,plain,
% 12.21/2.06      ( k3_enumset1(sK0,sK0,sK0,sK1,sK2) = k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
% 12.21/2.06      inference(instantiation,[status(thm)],[c_25]) ).
% 12.21/2.06  
% 12.21/2.06  cnf(c_2,plain,
% 12.21/2.06      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 12.21/2.06      inference(cnf_transformation,[],[f16]) ).
% 12.21/2.06  
% 12.21/2.06  cnf(c_22,plain,
% 12.21/2.06      ( k2_xboole_0(X0_40,X1_40) = k2_xboole_0(X1_40,X0_40) ),
% 12.21/2.06      inference(subtyping,[status(esa)],[c_2]) ).
% 12.21/2.06  
% 12.21/2.06  cnf(c_131,plain,
% 12.21/2.06      ( k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
% 12.21/2.06      inference(instantiation,[status(thm)],[c_22]) ).
% 12.21/2.06  
% 12.21/2.06  cnf(c_126,plain,
% 12.21/2.06      ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) = k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
% 12.21/2.06      inference(instantiation,[status(thm)],[c_25]) ).
% 12.21/2.06  
% 12.21/2.06  cnf(c_67,plain,
% 12.21/2.06      ( k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) ),
% 12.21/2.06      inference(instantiation,[status(thm)],[c_22]) ).
% 12.21/2.06  
% 12.21/2.06  cnf(c_46,plain,
% 12.21/2.06      ( k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != X0_40
% 12.21/2.06      | k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))
% 12.21/2.06      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != X0_40 ),
% 12.21/2.06      inference(instantiation,[status(thm)],[c_26]) ).
% 12.21/2.06  
% 12.21/2.06  cnf(c_66,plain,
% 12.21/2.06      ( k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3))
% 12.21/2.06      | k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))
% 12.21/2.06      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) ),
% 12.21/2.06      inference(instantiation,[status(thm)],[c_46]) ).
% 12.21/2.06  
% 12.21/2.06  cnf(c_6,negated_conjecture,
% 12.21/2.06      ( k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
% 12.21/2.06      inference(cnf_transformation,[],[f31]) ).
% 12.21/2.06  
% 12.21/2.06  cnf(c_18,negated_conjecture,
% 12.21/2.06      ( k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
% 12.21/2.06      inference(subtyping,[status(esa)],[c_6]) ).
% 12.21/2.06  
% 12.21/2.06  cnf(contradiction,plain,
% 12.21/2.06      ( $false ),
% 12.21/2.06      inference(minisat,
% 12.21/2.06                [status(thm)],
% 12.21/2.06                [c_46554,c_28490,c_28489,c_16586,c_5584,c_3533,c_2145,
% 12.21/2.06                 c_1865,c_954,c_846,c_368,c_367,c_288,c_214,c_144,c_131,
% 12.21/2.06                 c_126,c_67,c_66,c_18]) ).
% 12.21/2.06  
% 12.21/2.06  
% 12.21/2.06  % SZS output end CNFRefutation for theBenchmark.p
% 12.21/2.06  
% 12.21/2.06  ------                               Statistics
% 12.21/2.06  
% 12.21/2.06  ------ Selected
% 12.21/2.06  
% 12.21/2.06  total_time:                             1.491
% 12.21/2.06  
%------------------------------------------------------------------------------
